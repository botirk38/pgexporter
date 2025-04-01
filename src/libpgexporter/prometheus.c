/*
 * Copyright (C) 2025 The pgexporter community
 *
 * Redistribution and use in source and binary forms, with or without modification,
 * are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice, this list
 * of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice, this
 * list of conditions and the following disclaimer in the documentation and/or other
 * materials provided with the distribution.
 *
 * 3. Neither the name of the copyright holder nor the names of its contributors may
 * be used to endorse or promote products derived from this software without specific
 * prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY
 * EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES
 * OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL
 * THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT
 * OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR
 * TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

/* pgexporter */
#include "art.h"
#include "prometheus_client.h"
#include "value.h"
#include <pgexporter.h>
#include <logging.h>
#include <memory.h>
#include <message.h>
#include <network.h>
#include <prometheus.h>
#include <queries.h>
#include <query_alts.h>
#include <security.h>
#include <shmem.h>
#include <utils.h>

/* system */
#include <errno.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/types.h>

#define CHUNK_SIZE 32768

#define PAGE_UNKNOWN 0
#define PAGE_HOME    1
#define PAGE_METRICS 2
#define BAD_REQUEST  3

#define MAX_ARR_LENGTH 256
#define NUMBER_OF_HISTOGRAM_COLUMNS 4

#define INPUT_NO   0
#define INPUT_DATA 1
#define INPUT_WAL  2

/**
 * This is a linked list of queries with the data received from the server
 * as well as the query sent to the server and other meta data.
 **/
typedef struct query_list
{
   struct query* query;
   struct query_list* next;
   struct query_alts* query_alt;
   char tag[MISC_LENGTH];
   int sort_type;
   bool error;
} query_list_t;

/**
 * This is one of the nodes of a linked list of a column entry.
 *
 * Since columns are the fundamental unit in a metric and since
 * due to different versions of servers, each query might have
 * a variable structure, dividing each query into its constituent
 * columns is needed.
 *
 * Then each received tuple can have their individual column values
 * appended to the suitable linked list of `column_node_t`.
 **/
typedef struct column_node
{
   char* data;
   struct tuple* tuple;
   struct column_node* next;
} column_node_t;

/**
 * It stores the metadata of a `column_node_t` linked list.
 * Meant to be used as part of an array
 **/
typedef struct column_store
{
   column_node_t* columns;
   column_node_t* last_column;
   char tag[MISC_LENGTH];
   int type;
   char name[MISC_LENGTH];
   int sort_type;
} column_store_t;

static int resolve_page(struct message* msg);
static int badrequest_page(int client_fd);
static int unknown_page(int client_fd);
static int home_page(int client_fd);
static int metrics_page(int client_fd);
static int bad_request(int client_fd);

static bool collector_pass(const char* collector);


static void general_information(int client_fd, struct prometheus_bridge* bridge);
static void core_information(int client_fd, struct prometheus_bridge* bridge);
static void extension_information(int client_fd, struct prometheus_bridge* bridge);
static void extension_function(int client_fd, struct prometheus_bridge* bridge, char* function, int input, char* description, char* type);
static void server_information(int client_fd, struct prometheus_bridge* bridge);
static void version_information(int client_fd, struct prometheus_bridge* bridge);
static void uptime_information(int client_fd, struct prometheus_bridge* bridge);
static void primary_information(int client_fd, struct prometheus_bridge* bridge);
static void settings_information(int client_fd, struct prometheus_bridge* bridge);
static void custom_metrics(int client_fd, struct prometheus_bridge* bridge); // Handles custom metrics provided in YAML format, both internal and external

static void handle_histogram(struct prometheus_bridge* bridge, query_list_t* temp);
static void handle_gauge_counter(struct prometheus_bridge*,  query_list_t* temp);

static int send_chunk(int client_fd, char* data);
static int parse_list(char* list_str, char** strs, int* n_strs);

static char* get_value(char* tag, char* name, char* val);
static int safe_prometheus_key_additional_length(char* key);
static char* safe_prometheus_key(char* key);
static void safe_prometheus_key_free(char* key);

static bool is_metrics_cache_configured(void);
static bool is_metrics_cache_valid(void);
static bool metrics_cache_append(char* data);
static bool metrics_cache_finalize(void);
static size_t metrics_cache_size_to_alloc(void);
static void metrics_cache_invalidate(void);

void
pgexporter_prometheus(int client_fd)
{
   int status;
   int page;
   struct message* msg = NULL;
   struct configuration* config;

   pgexporter_start_logging();
   pgexporter_memory_init();

   config = (struct configuration*)shmem;

   status = pgexporter_read_timeout_message(NULL, client_fd, config->authentication_timeout, &msg);

   if (status != MESSAGE_STATUS_OK)
   {
      goto error;
   }

   page = resolve_page(msg);

   if (page == PAGE_HOME)
   {
      home_page(client_fd);
   }
   else if (page == PAGE_METRICS)
   {
      metrics_page(client_fd);
   }
   else if (page == PAGE_UNKNOWN)
   {
      unknown_page(client_fd);
   }
   else
   {
      bad_request(client_fd);
   }

   pgexporter_disconnect(client_fd);

   pgexporter_memory_destroy();
   pgexporter_stop_logging();

   exit(0);

error:

   badrequest_page(client_fd);

   pgexporter_disconnect(client_fd);

   pgexporter_memory_destroy();
   pgexporter_stop_logging();

   exit(1);
}

void
pgexporter_prometheus_reset(void)
{
   signed char cache_is_free;
   struct configuration* config;
   struct prometheus_cache* cache;

   config = (struct configuration*)shmem;
   cache = (struct prometheus_cache*)prometheus_cache_shmem;

retry_cache_locking:
   cache_is_free = STATE_FREE;
   if (atomic_compare_exchange_strong(&cache->lock, &cache_is_free, STATE_IN_USE))
   {
      metrics_cache_invalidate();

      atomic_store(&config->logging_info, 0);
      atomic_store(&config->logging_warn, 0);
      atomic_store(&config->logging_error, 0);
      atomic_store(&config->logging_fatal, 0);

      atomic_store(&cache->lock, STATE_FREE);
   }
   else
   {
      /* Sleep for 1ms */
      SLEEP_AND_GOTO(1000000L, retry_cache_locking);
   }
}

void
pgexporter_prometheus_logging(int type)
{
   struct configuration* config;

   config = (struct configuration*)shmem;

   switch (type)
   {
      case PGEXPORTER_LOGGING_LEVEL_INFO:
         atomic_fetch_add(&config->logging_info, 1);
         break;
      case PGEXPORTER_LOGGING_LEVEL_WARN:
         atomic_fetch_add(&config->logging_warn, 1);
         break;
      case PGEXPORTER_LOGGING_LEVEL_ERROR:
         atomic_fetch_add(&config->logging_error, 1);
         break;
      case PGEXPORTER_LOGGING_LEVEL_FATAL:
         atomic_fetch_add(&config->logging_fatal, 1);
         break;
      default:
         break;
   }
}

static int
resolve_page(struct message* msg)
{
   char* from = NULL;
   int index;

   if (msg->length < 3 || strncmp((char*)msg->data, "GET", 3) != 0)
   {
      pgexporter_log_debug("Prometheus: Not a GET request");
      return BAD_REQUEST;
   }

   index = 4;
   from = (char*)msg->data + index;

   while (pgexporter_read_byte(msg->data + index) != ' ')
   {
      index++;
   }

   pgexporter_write_byte(msg->data + index, '\0');

   if (strcmp(from, "/") == 0 || strcmp(from, "/index.html") == 0)
   {
      return PAGE_HOME;
   }
   else if (strcmp(from, "/metrics") == 0)
   {
      return PAGE_METRICS;
   }

   return PAGE_UNKNOWN;
}

static int
badrequest_page(int client_fd)
{
   char* data = NULL;
   time_t now;
   char time_buf[32];
   int status;
   struct message msg;

   memset(&msg, 0, sizeof(struct message));
   memset(&data, 0, sizeof(data));

   now = time(NULL);

   memset(&time_buf, 0, sizeof(time_buf));
   ctime_r(&now, &time_buf[0]);
   time_buf[strlen(time_buf) - 1] = 0;

   data = pgexporter_vappend(data, 4,
                             "HTTP/1.1 400 Bad Request\r\n",
                             "Date: ",
                             &time_buf[0],
                             "\r\n"
                             );

   msg.kind = 0;
   msg.length = strlen(data);
   msg.data = data;

   status = pgexporter_write_message(NULL, client_fd, &msg);

   free(data);

   return status;
}

static int
unknown_page(int client_fd)
{
   char* data = NULL;
   time_t now;
   char time_buf[32];
   int status;
   struct message msg;

   memset(&msg, 0, sizeof(struct message));
   memset(&data, 0, sizeof(data));

   now = time(NULL);

   memset(&time_buf, 0, sizeof(time_buf));
   ctime_r(&now, &time_buf[0]);
   time_buf[strlen(time_buf) - 1] = 0;

   data = pgexporter_vappend(data, 4,
                             "HTTP/1.1 403 Forbidden\r\n",
                             "Date: ",
                             &time_buf[0],
                             "\r\n"
                             );

   msg.kind = 0;
   msg.length = strlen(data);
   msg.data = data;

   status = pgexporter_write_message(NULL, client_fd, &msg);

   free(data);

   return status;
}

static int
home_page(int client_fd)
{
   char* data = NULL;
   int status;
   time_t now;
   char time_buf[32];
   struct message msg;
   struct configuration* config;

   config = (struct configuration*) shmem;

   now = time(NULL);

   memset(&time_buf, 0, sizeof(time_buf));
   ctime_r(&now, &time_buf[0]);
   time_buf[strlen(time_buf) - 1] = 0;

   data = pgexporter_vappend(data, 7,
                             "HTTP/1.1 200 OK\r\n",
                             "Content-Type: text/html; charset=utf-8\r\n",
                             "Date: ",
                             &time_buf[0],
                             "\r\n",
                             "Transfer-Encoding: chunked\r\n",
                             "\r\n"
                             );

   msg.kind = 0;
   msg.length = strlen(data);
   msg.data = data;

   status = pgexporter_write_message(NULL, client_fd, &msg);
   if (status != MESSAGE_STATUS_OK)
   {
      goto error;
   }

   free(data);
   data = NULL;

   data = pgexporter_vappend(data, 12,
                             "<html>\n",
                             "<head>\n",
                             "  <title>pgexporter</title>\n",
                             "</head>\n",
                             "<body>\n",
                             "  <h1>pgexporter</h1>\n",
                             "  Prometheus exporter for PostgreSQL\n",
                             "  <p>\n",
                             "  <a href=\"/metrics\">Metrics</a>\n",
                             "  <p>\n",
                             "  Support for\n",
                             "  <ul>\n"
                             );

   send_chunk(client_fd, data);
   free(data);
   data = NULL;

   data = pgexporter_vappend(data, 4,
                             "  <li>pgexporter_logging_info</li>\n",
                             "  <li>pgexporter_logging_warn</li>\n",
                             "  <li>pgexporter_logging_error</li>\n",
                             "  <li>pgexporter_logging_fatal</li>\n"
                             );

   send_chunk(client_fd, data);
   free(data);
   data = NULL;

   if (config->number_of_metrics == 0)
   {
      data = pgexporter_vappend(data, 7,
                                "  <li>pg_database</li>\n",
                                "  <li>pg_locks</li>\n",
                                "  <li>pg_replication_slots</li>\n",
                                "  <li>pg_settings</li>\n",
                                "  <li>pg_stat_bgwriter</li>\n",
                                "  <li>pg_stat_database</li>\n",
                                "  <li>pg_stat_database_conflicts</li>\n"
                                );
   }
   else
   {
      for (int i = 0; i < config->number_of_metrics; i++)
      {
         data = pgexporter_vappend(data, 3,
                                   "  <li>",
                                   config->prometheus[i].tag,
                                   "</li>\n"
                                   );
      }
   }

   send_chunk(client_fd, data);
   free(data);
   data = NULL;

   data = pgexporter_vappend(data, 5,
                             "  </ul>\n",
                             "  <p>\n",
                             "  <a href=\"https://pgexporter.github.io/\">pgexporter.github.io/</a>\n",
                             "</body>\n",
                             "</html>\n"
                             );

   /* Footer */
   data = pgexporter_append(data, "\r\n\r\n");

   send_chunk(client_fd, data);
   free(data);
   data = NULL;

   return 0;

error:

   free(data);

   return 1;
}



static int
metrics_page(int client_fd)
{
   char* data = NULL;
   time_t start_time;
   int dt;
   time_t now;
   char time_buf[32];
   int status;
   struct message msg;
   struct prometheus_cache* cache;
   signed char cache_is_free;
   struct configuration* config;
   struct prometheus_bridge* bridge = NULL;

   config = (struct configuration*)shmem;
   cache = (struct prometheus_cache*)prometheus_cache_shmem;

   memset(&msg, 0, sizeof(struct message));

   start_time = time(NULL);

retry_cache_locking:
   cache_is_free = STATE_FREE;
   if (atomic_compare_exchange_strong(&cache->lock, &cache_is_free, STATE_IN_USE))
   {
      // can serve the message out of cache?
      if (is_metrics_cache_configured() && is_metrics_cache_valid())
      {
         // serve the message directly out of the cache
         pgexporter_log_debug("Serving metrics out of cache (%d/%d bytes valid until %lld)",
                              strlen(cache->data),
                              cache->size,
                              cache->valid_until);

         msg.kind = 0;
         msg.length = strlen(cache->data);
         msg.data = cache->data;

         status = pgexporter_write_message(NULL, client_fd, &msg);
         if (status != MESSAGE_STATUS_OK)
         {
            goto error;
         }
      }
      else
      {
         // build the message without the cache
         metrics_cache_invalidate();

         now = time(NULL);

         memset(&time_buf, 0, sizeof(time_buf));
         ctime_r(&now, &time_buf[0]);
         time_buf[strlen(time_buf) - 1] = 0;

         data = pgexporter_vappend(data, 5,
                                   "HTTP/1.1 200 OK\r\n",
                                   "Content-Type: text/plain; version=0.0.1; charset=utf-8\r\n",
                                   "Date: ",
                                   &time_buf[0],
                                   "\r\n"
                                   );
         metrics_cache_append(data);  // cache here to avoid the chunking for the cache
         data = pgexporter_vappend(data, 2,
                                   "Transfer-Encoding: chunked\r\n",
                                   "\r\n"
                                   );

         msg.kind = 0;
         msg.length = strlen(data);
         msg.data = data;

         status = pgexporter_write_message(NULL, client_fd, &msg);
         if (status != MESSAGE_STATUS_OK)
         {
            goto error;
         }

         free(data);
         data = NULL;

         pgexporter_open_connections();

         /* Create the bridge */
         if (pgexporter_prometheus_client_create_bridge(&bridge))
         {
            goto error;
         }

         /* General Metric Collector */
         general_information(client_fd, bridge);
         core_information(client_fd, bridge);
         server_information(client_fd, bridge);
         version_information(client_fd, bridge);
         uptime_information(client_fd, bridge);
         primary_information(client_fd, bridge);
         settings_information(client_fd, bridge);
         extension_information(client_fd, bridge);

         custom_metrics(client_fd, bridge);

         /* Convert bridge to text format and send */
         struct art_iterator* metrics_iterator = NULL;
         if (pgexporter_art_iterator_create(bridge->metrics, &metrics_iterator))
         {
            goto error;
         }

         while (pgexporter_art_iterator_next(metrics_iterator))
         {
            struct prometheus_metric* metric_data = (struct prometheus_metric*)metrics_iterator->value->data;
            struct deque_iterator* definition_iterator = NULL;

            data = pgexporter_append(data, "#HELP ");
            data = pgexporter_append(data, metric_data->name);
            data = pgexporter_append_char(data, ' ');
            data = pgexporter_append(data, metric_data->help);
            data = pgexporter_append_char(data, '\n');

            data = pgexporter_append(data, "#TYPE ");
            data = pgexporter_append(data, metric_data->name);
            data = pgexporter_append_char(data, ' ');
            data = pgexporter_append(data, metric_data->type);
            data = pgexporter_append_char(data, '\n');

            if (pgexporter_deque_iterator_create(metric_data->definitions, &definition_iterator))
            {
               goto error;
            }

            while (pgexporter_deque_iterator_next(definition_iterator))
            {
               struct deque_iterator* attributes_iterator = NULL;
               struct prometheus_attributes* attrs_data = (struct prometheus_attributes*)definition_iterator->value->data;
               struct prometheus_value* value_data = NULL;

               if (pgexporter_deque_iterator_create(attrs_data->attributes, &attributes_iterator))
               {
                  goto error;
               }

               value_data = (struct prometheus_value*)pgexporter_deque_peek_last(attrs_data->values, NULL);

               data = pgexporter_append(data, metric_data->name);
               data = pgexporter_append_char(data, '{');

               while (pgexporter_deque_iterator_next(attributes_iterator))
               {
                  struct prometheus_attribute* attr_data = (struct prometheus_attribute*)attributes_iterator->value->data;

                  data = pgexporter_append(data, attr_data->key);
                  data = pgexporter_append(data, "=\"");
                  data = pgexporter_append(data, attr_data->value);
                  data = pgexporter_append_char(data, '\"');

                  if (pgexporter_deque_iterator_has_next(attributes_iterator))
                  {
                     data = pgexporter_append(data, ", ");
                  }
               }

               data = pgexporter_append(data, "} ");
               data = pgexporter_append(data, value_data->value);

               data = pgexporter_append_char(data, '\n');

               pgexporter_deque_iterator_destroy(attributes_iterator);
            }

            data = pgexporter_append_char(data, '\n');

            metrics_cache_append(data);
            send_chunk(client_fd, data);

            pgexporter_deque_iterator_destroy(definition_iterator);

            free(data);
            data = NULL;
         }

         pgexporter_art_iterator_destroy(metrics_iterator);
         pgexporter_prometheus_client_destroy_bridge(bridge);

         pgexporter_close_connections();

         /* Footer */
         data = pgexporter_append(data, "0\r\n\r\n");

         msg.kind = 0;
         msg.length = strlen(data);
         msg.data = data;

         status = pgexporter_write_message(NULL, client_fd, &msg);
         if (status != MESSAGE_STATUS_OK)
         {
            goto error;
         }

         metrics_cache_finalize();
      }

      // free the cache
      atomic_store(&cache->lock, STATE_FREE);
   }
   else
   {
      dt = (int)difftime(time(NULL), start_time);
      if (dt >= (config->blocking_timeout > 0 ? config->blocking_timeout : 30))
      {
         goto error;
      }

      /* Sleep for 10ms */
      SLEEP_AND_GOTO(10000000L, retry_cache_locking);
   }

   free(data);

   return 0;

error:
   if (bridge != NULL)
   {
      pgexporter_prometheus_client_destroy_bridge(bridge);
   }

   free(data);

   return 1;
}


static int
bad_request(int client_fd)
{
   char* data = NULL;
   time_t now;
   char time_buf[32];
   int status;
   struct message msg;

   memset(&msg, 0, sizeof(struct message));
   memset(&data, 0, sizeof(data));

   now = time(NULL);

   memset(&time_buf, 0, sizeof(time_buf));
   ctime_r(&now, &time_buf[0]);
   time_buf[strlen(time_buf) - 1] = 0;

   data = pgexporter_vappend(data, 4,
                             "HTTP/1.1 400 Bad Request\r\n",
                             "Date: ",
                             &time_buf[0],
                             "\r\n"
                             );

   msg.kind = 0;
   msg.length = strlen(data);
   msg.data = data;

   status = pgexporter_write_message(NULL, client_fd, &msg);

   free(data);

   return status;
}

static bool
collector_pass(const char* collector)
{
   struct configuration* config = NULL;

   config = (struct configuration*)shmem;

   if (config->number_of_collectors == 0)
   {
      return true;
   }

   for (int i = 0; i < config->number_of_collectors; i++)
   {
      if (!strcmp(config->collectors[i], collector))
      {
         return true;
      }
   }

   return false;
}

static void
general_information(int client_fd, struct prometheus_bridge* bridge)
{

   struct prometheus_metric* metric = NULL;
   struct prometheus_attributes* attrs = NULL;
   struct prometheus_value* val = NULL;
   struct configuration* config;
   config = (struct configuration*)shmem;


  /* pgexporter_state */
   metric = malloc(sizeof(struct prometheus_metric));
   memset(metric, 0, sizeof(struct prometheus_metric));
   
   metric->name = strdup("pgexporter_state");
   metric->help = strdup("The state of pgexporter");
   metric->type = strdup("gauge");
   
   pgexporter_deque_create(true, &metric->definitions);
   
   attrs = malloc(sizeof(struct prometheus_attributes));
   memset(attrs, 0, sizeof(struct prometheus_attributes));
   
   pgexporter_deque_create(true, &attrs->attributes);
   pgexporter_deque_create(true, &attrs->values);
   
   val = malloc(sizeof(struct prometheus_value));
   memset(val, 0, sizeof(struct prometheus_value));
   
   val->timestamp = time(NULL);
   val->value = strdup("1");
   
   pgexporter_deque_add(attrs->values, NULL, (uintptr_t)val, ValueRef );
   pgexporter_deque_add(metric->definitions, NULL, (uintptr_t)attrs, ValueRef);
   
   pgexporter_art_insert(bridge->metrics, metric->name, (uintptr_t)metric, ValueRef);

   /* pgexporter_logging_info */
   metric = malloc(sizeof(struct prometheus_metric));
   memset(metric, 0, sizeof(struct prometheus_metric));
   
   metric->name = strdup("pgexporter_logging_info");
   metric->help = strdup("The number of INFO logging statements");
   metric->type = strdup("gauge");
   
   pgexporter_deque_create(true, &metric->definitions);
   
   attrs = malloc(sizeof(struct prometheus_attributes));
   memset(attrs, 0, sizeof(struct prometheus_attributes));
   
   pgexporter_deque_create(true, &attrs->attributes);
   pgexporter_deque_create(true, &attrs->values);
   
   val = malloc(sizeof(struct prometheus_value));
   memset(val, 0, sizeof(struct prometheus_value));
   
   val->timestamp = time(NULL);
   val->value = malloc(32);
   sprintf(val->value, "%ld", atomic_load(&config->logging_info));
   
   pgexporter_deque_add(attrs->values, NULL, (uintptr_t)val, ValueRef);
   pgexporter_deque_add(metric->definitions, NULL, (uintptr_t)attrs, ValueRef);
   
   pgexporter_art_insert(bridge->metrics, metric->name, (uintptr_t)metric, ValueRef);

   /* pgexporter_logging_warn */
   metric = malloc(sizeof(struct prometheus_metric));
   memset(metric, 0, sizeof(struct prometheus_metric));
   
   metric->name = strdup("pgexporter_logging_warn");
   metric->help = strdup("The number of WARN logging statements");
   metric->type = strdup("gauge");
   
   pgexporter_deque_create(true, &metric->definitions);
   
   attrs = malloc(sizeof(struct prometheus_attributes));
   memset(attrs, 0, sizeof(struct prometheus_attributes));
   
   pgexporter_deque_create(true, &attrs->attributes);
   pgexporter_deque_create(true, &attrs->values);
   
   val = malloc(sizeof(struct prometheus_value));
   memset(val, 0, sizeof(struct prometheus_value));
   
   val->timestamp = time(NULL);
   val->value = malloc(32);
   sprintf(val->value, "%ld", atomic_load(&config->logging_warn));
   
   pgexporter_deque_add(attrs->values, NULL, (uintptr_t)val, ValueRef);
   pgexporter_deque_add(metric->definitions, NULL, (uintptr_t)attrs, ValueRef);
   
   pgexporter_art_insert(bridge->metrics, metric->name, (uintptr_t)metric, ValueRef);

   /* pgexporter_logging_error */
   metric = malloc(sizeof(struct prometheus_metric));
   memset(metric, 0, sizeof(struct prometheus_metric));
   
   metric->name = strdup("pgexporter_logging_error");
   metric->help = strdup("The number of ERROR logging statements");
   metric->type = strdup("gauge");
   
   pgexporter_deque_create(true, &metric->definitions);
   
   attrs = malloc(sizeof(struct prometheus_attributes));
   memset(attrs, 0, sizeof(struct prometheus_attributes));
   
   pgexporter_deque_create(true, &attrs->attributes);
   pgexporter_deque_create(true, &attrs->values);
   
   val = malloc(sizeof(struct prometheus_value));
   memset(val, 0, sizeof(struct prometheus_value));
   
   val->timestamp = time(NULL);
   val->value = malloc(32);
   sprintf(val->value, "%ld", atomic_load(&config->logging_error));
   
   pgexporter_deque_add(attrs->values, NULL, (uintptr_t)val, ValueRef);
   pgexporter_deque_add(metric->definitions, NULL, (uintptr_t)attrs, ValueRef);
   
   pgexporter_art_insert(bridge->metrics, metric->name, (uintptr_t)metric, ValueRef);

   /* pgexporter_logging_fatal */
   metric = malloc(sizeof(struct prometheus_metric));
   memset(metric, 0, sizeof(struct prometheus_metric));
   
   metric->name = strdup("pgexporter_logging_fatal");
   metric->help = strdup("The number of FATAL logging statements");
   metric->type = strdup("gauge");
   
   pgexporter_deque_create(true, &metric->definitions);
   
   attrs = malloc(sizeof(struct prometheus_attributes));
   memset(attrs, 0, sizeof(struct prometheus_attributes));
   
   pgexporter_deque_create(true, &attrs->attributes);
   pgexporter_deque_create(true, &attrs->values);
   
   val = malloc(sizeof(struct prometheus_value));
   memset(val, 0, sizeof(struct prometheus_value));
   
   val->timestamp = time(NULL);
   val->value = malloc(32);
   sprintf(val->value, "%ld", atomic_load(&config->logging_fatal));
   
   pgexporter_deque_add(attrs->values, NULL, (uintptr_t)val, ValueRef);
   pgexporter_deque_add(metric->definitions, NULL, (uintptr_t)attrs, ValueRef);
   
   pgexporter_art_insert(bridge->metrics, metric->name, (uintptr_t)metric, ValueRef);
}


static void
server_information(int client_fd, struct prometheus_bridge* bridge)
{
   struct prometheus_metric* metric = NULL;
   struct prometheus_attributes* attrs = NULL;
   struct prometheus_attribute* attr = NULL;
   struct prometheus_value* val = NULL;
   struct configuration* config;

   config = (struct configuration*)shmem;

   /* Create pgexporter_postgresql_active metric */
   metric = malloc(sizeof(struct prometheus_metric));
   memset(metric, 0, sizeof(struct prometheus_metric));
   
   metric->name = strdup("pgexporter_postgresql_active");
   metric->help = strdup("The state of PostgreSQL");
   metric->type = strdup("gauge");
   
   /* Create definitions deque - using thread_safe=false */
   pgexporter_deque_create(false, &metric->definitions);
   
   /* Add server attributes for each server */
   for (int server = 0; server < config->number_of_servers; server++)
   {
      attrs = malloc(sizeof(struct prometheus_attributes));
      memset(attrs, 0, sizeof(struct prometheus_attributes));
      
      /* Create attributes and values deques */
      pgexporter_deque_create(false, &attrs->attributes);
      pgexporter_deque_create(false, &attrs->values);
      
      /* Add server attribute */
      attr = malloc(sizeof(struct prometheus_attribute));
      memset(attr, 0, sizeof(struct prometheus_attribute));
      
      attr->key = strdup("server");
      attr->value = strdup(config->servers[server].name);
      
      /* Add attribute to attributes deque */
      pgexporter_deque_add(attrs->attributes, NULL, (uintptr_t)attr, ValueRef);
      
      /* Create value */
      val = malloc(sizeof(struct prometheus_value));
      memset(val, 0, sizeof(struct prometheus_value));
      
      val->timestamp = time(NULL);
      
      /* Set value based on server state */
      if (config->servers[server].fd != -1)
      {
         val->value = strdup("1");
      }
      else
      {
         val->value = strdup("0");
      }
      
      /* Add value to values deque */
      pgexporter_deque_add(attrs->values, NULL, (uintptr_t)val, ValueRef);
      
      /* Add attributes to definitions */
      pgexporter_deque_add(metric->definitions, NULL, (uintptr_t)attrs, ValueRef);
   }
   
   /* Add metric to bridge */
   pgexporter_art_insert(bridge->metrics, metric->name, (uintptr_t)metric, ValueRef);
}


static void
version_information(int client_fd, struct prometheus_bridge* bridge)
{
   int ret;
   int server;
   char* safe_key1 = NULL;
   char* safe_key2 = NULL;
   struct query* all = NULL;
   struct query* query = NULL;
   struct tuple* current = NULL;
   struct configuration* config;
   struct prometheus_metric* metric = NULL;
   struct prometheus_attributes* attrs = NULL;
   struct prometheus_attribute* attr = NULL;
   struct prometheus_value* val = NULL;

   config = (struct configuration*)shmem;

   for (server = 0; server < config->number_of_servers; server++)
   {
      if (config->servers[server].fd != -1)
      {
         ret = pgexporter_query_version(server, &query);
         if (ret == 0)
         {
            all = pgexporter_merge_queries(all, query, SORT_NAME);
         }
         query = NULL;
      }
   }

   if (all != NULL)
   {
      current = all->tuples;
      if (current != NULL)
      {
         /* Create pgexporter_postgresql_version metric */
         metric = malloc(sizeof(struct prometheus_metric));
         memset(metric, 0, sizeof(struct prometheus_metric));
         
         metric->name = strdup("pgexporter_postgresql_version");
         metric->help = strdup("The PostgreSQL version");
         metric->type = strdup("gauge");
         
         pgexporter_deque_create(false, &metric->definitions);
         
         server = 0;
         
         while (current != NULL)
         {
            /* Create attributes for this server */
            attrs = malloc(sizeof(struct prometheus_attributes));
            memset(attrs, 0, sizeof(struct prometheus_attributes));
            
            pgexporter_deque_create(false, &attrs->attributes);
            pgexporter_deque_create(false, &attrs->values);
            
            /* Add server attribute */
            attr = malloc(sizeof(struct prometheus_attribute));
            memset(attr, 0, sizeof(struct prometheus_attribute));
            
            attr->key = strdup("server");
            attr->value = strdup(config->servers[server].name);
            
            pgexporter_deque_add(attrs->attributes, NULL, (uintptr_t)attr, ValueRef);
            
            /* Add version attribute */
            attr = malloc(sizeof(struct prometheus_attribute));
            memset(attr, 0, sizeof(struct prometheus_attribute));
            
            attr->key = strdup("version");
            safe_key1 = safe_prometheus_key(pgexporter_get_column(0, current));
            attr->value = strdup(safe_key1);
            
            pgexporter_deque_add(attrs->attributes, NULL, (uintptr_t)attr, ValueRef);
            
            /* Add minor_version attribute */
            attr = malloc(sizeof(struct prometheus_attribute));
            memset(attr, 0, sizeof(struct prometheus_attribute));
            
            attr->key = strdup("minor_version");
            safe_key2 = safe_prometheus_key(pgexporter_get_column(1, current));
            attr->value = strdup(safe_key2);
            
            pgexporter_deque_add(attrs->attributes, NULL, (uintptr_t)attr, ValueRef);
            
            /* Create value */
            val = malloc(sizeof(struct prometheus_value));
            memset(val, 0, sizeof(struct prometheus_value));
            
            val->timestamp = time(NULL);
            val->value = strdup("1");
            
            pgexporter_deque_add(attrs->values, NULL, (uintptr_t)val, ValueRef);
            
            /* Add attributes to definitions */
            pgexporter_deque_add(metric->definitions, NULL, (uintptr_t)attrs, ValueRef);
            
            safe_prometheus_key_free(safe_key1);
            safe_prometheus_key_free(safe_key2);
            
            server++;
            current = current->next;
         }
         
         /* Add metric to bridge */
         pgexporter_art_insert(bridge->metrics, metric->name, (uintptr_t)metric, ValueRef);
      }
   }

   pgexporter_free_query(all);
}



static void
uptime_information(int client_fd, struct prometheus_bridge* bridge)
{
   int ret;
   int server;
   char* safe_key = NULL;
   struct query* all = NULL;
   struct query* query = NULL;
   struct tuple* current = NULL;
   struct configuration* config;
   struct prometheus_metric* metric = NULL;
   struct prometheus_attributes* attrs = NULL;
   struct prometheus_attribute* attr = NULL;
   struct prometheus_value* val = NULL;

   config = (struct configuration*)shmem;

   for (server = 0; server < config->number_of_servers; server++)
   {
      if (config->servers[server].fd != -1)
      {
         ret = pgexporter_query_uptime(server, &query);
         if (ret == 0)
         {
            all = pgexporter_merge_queries(all, query, SORT_NAME);
         }
         query = NULL;
      }
   }

   if (all != NULL)
   {
      current = all->tuples;
      if (current != NULL)
      {
         /* Create pgexporter_postgresql_uptime metric */
         metric = malloc(sizeof(struct prometheus_metric));
         memset(metric, 0, sizeof(struct prometheus_metric));
         
         metric->name = strdup("pgexporter_postgresql_uptime");
         metric->help = strdup("The PostgreSQL uptime in seconds");
         metric->type = strdup("counter");
         
         pgexporter_deque_create(false, &metric->definitions);
         
         server = 0;

         while (current != NULL)
         {
            attrs = malloc(sizeof(struct prometheus_attributes));
            memset(attrs, 0, sizeof(struct prometheus_attributes));
            
            pgexporter_deque_create(false, &attrs->attributes);
            pgexporter_deque_create(false, &attrs->values);
            
            /* Add server attribute */
            attr = malloc(sizeof(struct prometheus_attribute));
            memset(attr, 0, sizeof(struct prometheus_attribute));
            
            attr->key = strdup("server");
            attr->value = strdup(config->servers[server].name);
            
            pgexporter_deque_add(attrs->attributes, NULL, (uintptr_t)attr, ValueRef);
            
            /* Create value */
            val = malloc(sizeof(struct prometheus_value));
            memset(val, 0, sizeof(struct prometheus_value));
            
            val->timestamp = time(NULL);
            
            safe_key = safe_prometheus_key(pgexporter_get_column(0, current));
            val->value = strdup(safe_key);
            safe_prometheus_key_free(safe_key);
            
            pgexporter_deque_add(attrs->values, NULL, (uintptr_t)val, ValueRef);
            
            /* Add attributes to definitions */
            pgexporter_deque_add(metric->definitions, NULL, (uintptr_t)attrs, ValueRef);
            
            server++;
            current = current->next;
         }
         
         /* Add metric to bridge */
         pgexporter_art_insert(bridge->metrics, metric->name, (uintptr_t)metric, ValueRef);
      }
   }

   pgexporter_free_query(all);
}

static void
primary_information(int client_fd, struct prometheus_bridge* bridge)
{
   int ret;
   int server;
   struct query* all = NULL;
   struct query* query = NULL;
   struct tuple* current = NULL;
   struct configuration* config;
   struct prometheus_metric* metric = NULL;
   struct prometheus_attributes* attrs = NULL;
   struct prometheus_attribute* attr = NULL;
   struct prometheus_value* val = NULL;

   config = (struct configuration*)shmem;

   for (server = 0; server < config->number_of_servers; server++)
   {
      if (config->servers[server].fd != -1)
      {
         ret = pgexporter_query_primary(server, &query);
         if (ret == 0)
         {
            all = pgexporter_merge_queries(all, query, SORT_NAME);
         }
         query = NULL;
      }
   }

   if (all != NULL)
   {
      current = all->tuples;
      if (current != NULL)
      {
         /* Create pgexporter_postgresql_primary metric */
         metric = malloc(sizeof(struct prometheus_metric));
         memset(metric, 0, sizeof(struct prometheus_metric));
         
         metric->name = strdup("pgexporter_postgresql_primary");
         metric->help = strdup("Is the PostgreSQL instance the primary");
         metric->type = strdup("gauge");
         
         pgexporter_deque_create(false, &metric->definitions);
         
         server = 0;

         while (current != NULL)
         {
            attrs = malloc(sizeof(struct prometheus_attributes));
            memset(attrs, 0, sizeof(struct prometheus_attributes));
            
            pgexporter_deque_create(false, &attrs->attributes);
            pgexporter_deque_create(false, &attrs->values);
            
            /* Add server attribute */
            attr = malloc(sizeof(struct prometheus_attribute));
            memset(attr, 0, sizeof(struct prometheus_attribute));
            
            attr->key = strdup("server");
            attr->value = strdup(config->servers[server].name);
            
            pgexporter_deque_add(attrs->attributes, NULL, (uintptr_t)attr, ValueRef);
            
            /* Create value */
            val = malloc(sizeof(struct prometheus_value));
            memset(val, 0, sizeof(struct prometheus_value));
            
            val->timestamp = time(NULL);
            
            /* Set value based on primary status */
            if (!strcmp("t", pgexporter_get_column(0, current)))
            {
               val->value = strdup("1");
            }
            else
            {
               val->value = strdup("0");
            }
            
            pgexporter_deque_add(attrs->values, NULL, (uintptr_t)val, ValueRef);
            
            /* Add attributes to definitions */
            pgexporter_deque_add(metric->definitions, NULL, (uintptr_t)attrs, ValueRef);
            
            server++;
            current = current->next;
         }
         
         /* Add metric to bridge */
         pgexporter_art_insert(bridge->metrics, metric->name, (uintptr_t)metric, ValueRef);
      }
   }

   pgexporter_free_query(all);
}


static void
core_information(int client_fd, struct prometheus_bridge* bridge)
{
   struct prometheus_metric* metric = NULL;
   struct prometheus_attributes* attrs = NULL;
   struct prometheus_attribute* attr = NULL;
   struct prometheus_value* val = NULL;

   /* Create pgexporter_version metric */
   metric = malloc(sizeof(struct prometheus_metric));
   memset(metric, 0, sizeof(struct prometheus_metric));
   
   metric->name = strdup("pgexporter_version");
   metric->help = strdup("The pgexporter version");
   metric->type = strdup("counter");
   
   /* Create definitions deque */
   pgexporter_deque_create(false, &metric->definitions);
   
   /* Create attributes */
   attrs = malloc(sizeof(struct prometheus_attributes));
   memset(attrs, 0, sizeof(struct prometheus_attributes));
   
   pgexporter_deque_create(false, &attrs->attributes);
   pgexporter_deque_create(false, &attrs->values);
   
   /* Add pgexporter_version attribute */
   attr = malloc(sizeof(struct prometheus_attribute));
   memset(attr, 0, sizeof(struct prometheus_attribute));
   
   attr->key = strdup("pgexporter_version");
   attr->value = strdup(VERSION);
   
   /* Add attribute to attributes deque */
   pgexporter_deque_add(attrs->attributes, NULL, (uintptr_t)attr, ValueRef);
   
   /* Create value */
   val = malloc(sizeof(struct prometheus_value));
   memset(val, 0, sizeof(struct prometheus_value));
   
   val->timestamp = time(NULL);
   val->value = strdup("1");
   
   /* Add value to values deque */
   pgexporter_deque_add(attrs->values, NULL, (uintptr_t)val, ValueRef);
   
   /* Add attributes to definitions */
   pgexporter_deque_add(metric->definitions, NULL, (uintptr_t)attrs, ValueRef);
   
   /* Add metric to bridge */
   pgexporter_art_insert(bridge->metrics, metric->name, (uintptr_t)metric, ValueRef);
}



static void
extension_information(int client_fd, struct prometheus_bridge* bridge)
{
   bool cont = true;
   struct query* query = NULL;
   struct tuple* tuple = NULL;
   struct configuration* config;

   config = (struct configuration*)shmem;

   /* Expose only if default or specified */
   if (!collector_pass("extension"))
   {
      pgexporter_log_debug("extension_information disabled");
      return;
   }

   for (int server = 0; cont && server < config->number_of_servers; server++)
   {
      if (config->servers[server].extension && config->servers[server].fd != -1)
      {
         pgexporter_query_get_functions(server, &query);

         if (query != NULL)
         {
            tuple = query->tuples;

            while (tuple != NULL)
            {
               if (!strcmp(tuple->data[1], "f") || !strcmp(tuple->data[1], "false"))
               {
                  if (strcmp(tuple->data[0], "pgexporter_get_functions"))
                  {
                     extension_function(client_fd, bridge, tuple->data[0], false, tuple->data[2], tuple->data[3]);
                  }
               }
               else
               {
                  if (strcmp(tuple->data[0], "pgexporter_is_supported"))
                  {
                     extension_function(client_fd, bridge, tuple->data[0], INPUT_DATA, tuple->data[2], tuple->data[3]);
                     extension_function(client_fd, bridge, tuple->data[0], INPUT_WAL, tuple->data[2], tuple->data[3]);
                  }
               }

               tuple = tuple->next;
            }

            cont = false;
         }
         else
         {
            config->servers[server].extension = false;
            pgexporter_log_trace("extension_information disabled for server %d", server);
         }

         pgexporter_free_query(query);
         query = NULL;
      }
   }
}

static void
extension_function(int client_fd, struct prometheus_bridge* bridge, char* function, int input, char* description, char* type)
{
   char* sql = NULL;
   struct query* query = NULL;
   struct tuple* tuple = NULL;
   struct configuration* config;
   struct prometheus_metric* metric = NULL;
   struct prometheus_attributes* attrs = NULL;
   struct prometheus_attribute* attr = NULL;
   struct prometheus_value* val = NULL;
   char metric_name[256];

   config = (struct configuration*)shmem;

   /* Create metric name based on function and input type */
   if (input == INPUT_DATA)
   {
      snprintf(metric_name, sizeof(metric_name), "%s_data", function);
   }
   else if (input == INPUT_WAL)
   {
      snprintf(metric_name, sizeof(metric_name), "%s_wal", function);
   }
   else
   {
      snprintf(metric_name, sizeof(metric_name), "%s", function);
   }

   /* Create metric */
   metric = malloc(sizeof(struct prometheus_metric));
   memset(metric, 0, sizeof(struct prometheus_metric));
   
   metric->name = strdup(metric_name);
   metric->help = strdup(description);
   metric->type = strdup(type);
   
   pgexporter_deque_create(false, &metric->definitions);

   for (int server = 0; server < config->number_of_servers; server++)
   {
      if (config->servers[server].extension && config->servers[server].fd != -1)
      {
         bool execute = true;

         sql = pgexporter_append(sql, "SELECT * FROM ");
         sql = pgexporter_append(sql, function);
         sql = pgexporter_append_char(sql, '(');

         if (input != INPUT_NO)
         {
            if (input == INPUT_DATA && strlen(config->servers[server].data) > 0)
            {
               sql = pgexporter_append_char(sql, '\'');
               sql = pgexporter_append(sql, config->servers[server].data);
               sql = pgexporter_append_char(sql, '\'');
            }
            else if (input == INPUT_WAL && strlen(config->servers[server].wal) > 0)
            {
               sql = pgexporter_append_char(sql, '\'');
               sql = pgexporter_append(sql, config->servers[server].wal);
               sql = pgexporter_append_char(sql, '\'');
            }
            else
            {
               execute = false;
            }
         }
         sql = pgexporter_append(sql, ");");

         if (execute)
         {
            pgexporter_query_execute(server, sql, "pgexporter_ext", &query);
         }

         if (query == NULL)
         {
            config->servers[server].extension = false;
            free(sql);
            sql = NULL;
            continue;
         }

         config->servers[server].extension = true;

         tuple = query->tuples;

         while (tuple != NULL)
         {
            attrs = malloc(sizeof(struct prometheus_attributes));
            memset(attrs, 0, sizeof(struct prometheus_attributes));
            
            pgexporter_deque_create(false, &attrs->attributes);
            pgexporter_deque_create(false, &attrs->values);
            
            /* Add server attribute */
            attr = malloc(sizeof(struct prometheus_attribute));
            memset(attr, 0, sizeof(struct prometheus_attribute));
            
            attr->key = strdup("server");
            attr->value = strdup(config->servers[server].name);
            
            pgexporter_deque_add(attrs->attributes, NULL, (uintptr_t)attr, ValueRef);

            if (input != INPUT_NO)
            {
               /* Add location attribute */
               attr = malloc(sizeof(struct prometheus_attribute));
               memset(attr, 0, sizeof(struct prometheus_attribute));
               
               attr->key = strdup("location");
               
               if (input == INPUT_DATA)
               {
                  attr->value = strdup(config->servers[server].data);
               }
               else if (input == INPUT_WAL)
               {
                  attr->value = strdup(config->servers[server].wal);
               }
               
               pgexporter_deque_add(attrs->attributes, NULL, (uintptr_t)attr, ValueRef);
               
               /* Create value */
               val = malloc(sizeof(struct prometheus_value));
               memset(val, 0, sizeof(struct prometheus_value));
               
               val->timestamp = time(NULL);
               val->value = strdup(tuple->data[0]);
               
               pgexporter_deque_add(attrs->values, NULL, (uintptr_t)val, ValueRef);
            }
            else
            {
               /* Add column attributes */
               for (int col = 0; col < query->number_of_columns; col++)
               {
                  attr = malloc(sizeof(struct prometheus_attribute));
                  memset(attr, 0, sizeof(struct prometheus_attribute));
                  
                  attr->key = strdup(query->names[col]);
                  attr->value = strdup(tuple->data[col]);
                  
                  pgexporter_deque_add(attrs->attributes, NULL, (uintptr_t)attr, ValueRef);
               }
               
               /* Create value with constant 1 */
               val = malloc(sizeof(struct prometheus_value));
               memset(val, 0, sizeof(struct prometheus_value));
               
               val->timestamp = time(NULL);
               val->value = strdup("1");
               
               pgexporter_deque_add(attrs->values, NULL, (uintptr_t)val, ValueRef);
            }
            
            /* Add attributes to definitions */
            pgexporter_deque_add(metric->definitions, NULL, (uintptr_t)attrs, ValueRef);
            
            tuple = tuple->next;
         }

         free(sql);
         sql = NULL;

         pgexporter_free_query(query);
         query = NULL;
      }
   }

   /* Add metric to bridge */
   pgexporter_art_insert(bridge->metrics, metric->name, (uintptr_t)metric, ValueRef);
}


static void
settings_information(int client_fd, struct prometheus_bridge* bridge)
{
   int ret;
   char* safe_key = NULL;
   struct query* all = NULL;
   struct query* query = NULL;
   struct tuple* current = NULL;
   struct configuration* config;
   struct prometheus_metric* metric = NULL;
   struct prometheus_attributes* attrs = NULL;
   struct prometheus_attribute* attr = NULL;
   struct prometheus_value* val = NULL;

   config = (struct configuration*)shmem;

   /* Expose only if default or specified */
   if (!collector_pass("settings"))
   {
      return;
   }

   for (int server = 0; server < config->number_of_servers; server++)
   {
      if (config->servers[server].fd != -1)
      {
         ret = pgexporter_query_settings(server, &query);
         if (ret == 0)
         {
            all = pgexporter_merge_queries(all, query, SORT_DATA0);
         }
         query = NULL;
      }
   }

   if (all != NULL)
   {
      current = all->tuples;
      while (current != NULL)
      {
         safe_key = safe_prometheus_key(pgexporter_get_column(0, current));
         
         /* Create metric for this setting */
         char metric_name[256];
         snprintf(metric_name, sizeof(metric_name), "pgexporter_%s_%s", all->tag, safe_key);
         
         /* Check if metric already exists in the bridge */
         uintptr_t existing = pgexporter_art_search(bridge->metrics, metric_name);
         if (existing != 0)
         {
            /* Metric already exists, add another server's data */
            metric = (struct prometheus_metric*)existing;
         }
         else
         {
            /* Create new metric */
            metric = malloc(sizeof(struct prometheus_metric));
            memset(metric, 0, sizeof(struct prometheus_metric));
            
            metric->name = strdup(metric_name);
            metric->help = strdup(pgexporter_get_column(2, current));
            metric->type = strdup("gauge");
            
            pgexporter_deque_create(false, &metric->definitions);
            
            /* Add to bridge */
            pgexporter_art_insert(bridge->metrics, metric_name, (uintptr_t)metric, ValueRef);
         }
         
         /* Process all servers with this setting */
         while (current != NULL && 
                (current->next == NULL || 
                 strcmp(pgexporter_get_column(0, current), pgexporter_get_column(0, current->next)) == 0))
         {
            attrs = malloc(sizeof(struct prometheus_attributes));
            memset(attrs, 0, sizeof(struct prometheus_attributes));
            
            pgexporter_deque_create(false, &attrs->attributes);
            pgexporter_deque_create(false, &attrs->values);
            
            /* Add server attribute */
            attr = malloc(sizeof(struct prometheus_attribute));
            memset(attr, 0, sizeof(struct prometheus_attribute));
            
            attr->key = strdup("server");
            attr->value = strdup(config->servers[current->server].name);
            
            pgexporter_deque_add(attrs->attributes, NULL, (uintptr_t)attr, ValueRef);
            
            /* Create value */
            val = malloc(sizeof(struct prometheus_value));
            memset(val, 0, sizeof(struct prometheus_value));
            
            val->timestamp = time(NULL);
            val->value = strdup(get_value(all->tag, pgexporter_get_column(0, current), pgexporter_get_column(1, current)));
            
            pgexporter_deque_add(attrs->values, NULL, (uintptr_t)val, ValueRef);
            
            /* Add attributes to definitions */
            pgexporter_deque_add(metric->definitions, NULL, (uintptr_t)attrs, ValueRef);
            
            if (current->next != NULL && 
                strcmp(pgexporter_get_column(0, current), pgexporter_get_column(0, current->next)) == 0)
            {
               current = current->next;
            }
            else
            {
               break;
            }
         }
         
         safe_prometheus_key_free(safe_key);
         current = current->next;
      }
   }

   pgexporter_free_query(all);
}



static void
custom_metrics(int client_fd, struct prometheus_bridge* bridge)
{
   struct configuration* config = NULL;

   config = (struct configuration*)shmem;

   query_list_t* q_list = NULL;
   query_list_t* temp = q_list;

   // Iterate through each metric to send its query to PostgreSQL server
   for (int i = 0; i < config->number_of_metrics; i++)
   {
      struct prometheus* prom = &config->prometheus[i];

      /* Expose only if default or specified */
      if (!collector_pass(prom->collector))
      {
         continue;
      }

      // Iterate through each server and send appropriate query to PostgreSQL server
      for (int server = 0; server < config->number_of_servers; server++)
      {
         if (config->servers[server].fd == -1)
         {
            /* Skip */
            continue;
         }

         if ((prom->server_query_type == SERVER_QUERY_PRIMARY && config->servers[server].state != SERVER_PRIMARY) ||
             (prom->server_query_type == SERVER_QUERY_REPLICA && config->servers[server].state != SERVER_REPLICA))
         {
            /* Skip */
            continue;
         }

         struct query_alts* query_alt = pgexporter_get_query_alt(prom->root, server);

         if (!query_alt)
         {
            /* Skip */
            continue;
         }

         // Setting Temp's value
         query_list_t* next = malloc(sizeof(query_list_t));
         memset(next, 0, sizeof(query_list_t));

         if (!q_list)
         {
            q_list = next;
            temp = q_list;
         }
         else if (temp && temp->query)
         {
            temp->next = next;
            temp = next;
         }
         else if (temp && !temp->query)
         {
            free(next);
            next = NULL;
            memset(temp, 0, sizeof(query_list_t));
         }

         /* Names */
         char** names = malloc(query_alt->n_columns * sizeof(char*));
         for (int j = 0; j < query_alt->n_columns; j++)
         {
            names[j] = query_alt->columns[j].name;
         }
         memcpy(temp->tag, prom->tag, MISC_LENGTH);
         temp->query_alt = query_alt;

         // Gather all the queries in a linked list, with each query's result (linked list of tuples in it) as a node.
         if (query_alt->is_histogram)
         {
            temp->error = pgexporter_custom_query(server, query_alt->query, prom->tag, -1, NULL, &temp->query);
            temp->sort_type = prom->sort_type;
         }
         else
         {
            temp->error = pgexporter_custom_query(server, query_alt->query, prom->tag, query_alt->n_columns, names, &temp->query);
            temp->sort_type = prom->sort_type;
         }

         free(names);
         names = NULL;
      }
   }

   /* Process query results */
   temp = q_list;
   while (temp)
   {
      if (temp->error || (temp->query != NULL && temp->query->tuples != NULL))
      {
         if (temp->query_alt->is_histogram)
         {
        handle_histogram(bridge, temp);
         } else {
        handle_gauge_counter(bridge, temp);
         
      }
         
      }
      temp = temp->next;
   }

   /* Clean up */
   temp = q_list;
   query_list_t* last = NULL;
   while (temp)
   {
      pgexporter_free_query(temp->query);
      // temp->query_alt // Not freed here, but when program ends

      last = temp;
      temp = temp->next;
      last->next = NULL;

      free(last);
   }
   q_list = NULL;
}

static void
handle_gauge_counter(struct prometheus_bridge* bridge, query_list_t* temp)
{
   struct configuration* config;
   struct prometheus_metric* metric = NULL;
   struct prometheus_attributes* attrs = NULL;
   struct prometheus_attribute* attr = NULL;
   struct prometheus_value* val = NULL;
   char metric_name[256];
   
   config = (struct configuration*)shmem;

   if (!temp || !temp->query || !temp->query->tuples)
   {
      /* Skip */
      return;
   }

   for (int i = 0; i < temp->query_alt->n_columns; i++)
   {
      if (temp->query_alt->columns[i].type == LABEL_TYPE)
      {
         /* Dealt with later */
         continue;
      }

      /* Create metric name */
      if (strlen(temp->query_alt->columns[i].name) > 0)
      {
         snprintf(metric_name, sizeof(metric_name), "pgexporter_%s_%s", temp->tag, temp->query_alt->columns[i].name);
      }
      else
      {
         snprintf(metric_name, sizeof(metric_name), "pgexporter_%s", temp->tag);
      }

      /* Check if metric already exists in the bridge */
      uintptr_t existing = pgexporter_art_search(bridge->metrics, metric_name);
      if (existing != 0)
      {
         /* Metric already exists, use it */
         metric = (struct prometheus_metric*)existing;
      }
      else
      {
         /* Create new metric */
         metric = malloc(sizeof(struct prometheus_metric));
         memset(metric, 0, sizeof(struct prometheus_metric));
         
         metric->name = strdup(metric_name);
         metric->help = strdup(temp->query_alt->columns[i].description);
         
         /* Set metric type based on column type */
         if (temp->query_alt->columns[i].type == GAUGE_TYPE)
         {
            metric->type = strdup("gauge");
         }
         else if (temp->query_alt->columns[i].type == COUNTER_TYPE)
         {
            metric->type = strdup("counter");
         }
         else
         {
            /* Default to gauge */
            metric->type = strdup("gauge");
         }
         
         pgexporter_deque_create(false, &metric->definitions);
         
         /* Add to bridge */
         pgexporter_art_insert(bridge->metrics, metric_name, (uintptr_t)metric, ValueRef);
      }

      /* Process all tuples */
      struct tuple* tuple = temp->query->tuples;
      while (tuple)
      {
         attrs = malloc(sizeof(struct prometheus_attributes));
         memset(attrs, 0, sizeof(struct prometheus_attributes));
         
         pgexporter_deque_create(false, &attrs->attributes);
         pgexporter_deque_create(false, &attrs->values);
         
         /* Add server attribute */
         attr = malloc(sizeof(struct prometheus_attribute));
         memset(attr, 0, sizeof(struct prometheus_attribute));
         
         attr->key = strdup("server");
         attr->value = strdup(config->servers[tuple->server].name);
         
         pgexporter_deque_add(attrs->attributes, NULL, (uintptr_t)attr, ValueRef);
         
         /* Add label attributes */
         for (int j = 0; j < temp->query_alt->n_columns; j++)
         {
            if (temp->query_alt->columns[j].type != LABEL_TYPE)
            {
               continue;
            }
            
            attr = malloc(sizeof(struct prometheus_attribute));
            memset(attr, 0, sizeof(struct prometheus_attribute));
            
            attr->key = strdup(temp->query_alt->columns[j].name);
            
            /* Use safe_prometheus_key for label values */
            char* safe_key = safe_prometheus_key(pgexporter_get_column(j, tuple));
            attr->value = strdup(safe_key);
            safe_prometheus_key_free(safe_key);
            
            pgexporter_deque_add(attrs->attributes, NULL, (uintptr_t)attr, ValueRef);
         }
         
         /* Add value */
         val = malloc(sizeof(struct prometheus_value));
         memset(val, 0, sizeof(struct prometheus_value));
         
         val->timestamp = time(NULL);
         
         /* Use get_value to convert the value appropriately */
         char* value_str = get_value(temp->tag, 
                                    temp->query_alt->columns[i].name, 
                                    pgexporter_get_column(i, tuple));
         val->value = strdup(value_str);
         
         pgexporter_deque_add(attrs->values, NULL, (uintptr_t)val, ValueRef);
         
         /* Add attributes to definitions */
         pgexporter_deque_add(metric->definitions, NULL, (uintptr_t)attrs, ValueRef);
         
         tuple = tuple->next;
      }
   }
}



static void
handle_histogram(struct prometheus_bridge* bridge, query_list_t* temp)
{
   int n_bounds = 0;
   int n_buckets = 0;
   char* bounds_arr[MAX_ARR_LENGTH] = {0};
   char* buckets_arr[MAX_ARR_LENGTH] = {0};
   struct configuration* config;
   struct prometheus_metric* bucket_metric = NULL;
   struct prometheus_metric* sum_metric = NULL;
   struct prometheus_metric* count_metric = NULL;
   struct prometheus_attributes* attrs = NULL;
   struct prometheus_attribute* attr = NULL;
   struct prometheus_value* val = NULL;
   char metric_name[256];

   config = (struct configuration*)shmem;

   int h_idx = 0;
   for (; h_idx < temp->query_alt->n_columns; h_idx++)
   {
      if (temp->query_alt->columns[h_idx].type == HISTOGRAM_TYPE)
      {
         break;
      }
   }

   if (!temp || !temp->query || !temp->query->tuples)
   {
      return;
   }

   struct tuple* tp = temp->query->tuples;

   if (!tp)
   {
      return;
   }

   char* names[4] = {0};

   /* generate column names X_sum, X_count, X, X_bucket*/
   names[0] = pgexporter_vappend(names[0], 2,
                                 temp->query_alt->columns[h_idx].name,
                                 "_sum"
                                 );
   names[1] = pgexporter_vappend(names[1], 2,
                                 temp->query_alt->columns[h_idx].name,
                                 "_count"
                                 );
   names[2] = pgexporter_vappend(names[2], 1,
                                 temp->query_alt->columns[h_idx].name
                                 );
   names[3] = pgexporter_vappend(names[3], 2,
                                 temp->query_alt->columns[h_idx].name,
                                 "_bucket"
                                 );

   /* Create bucket metric */
   snprintf(metric_name, sizeof(metric_name), "pgexporter_%s_bucket", temp->tag);
   bucket_metric = malloc(sizeof(struct prometheus_metric));
   memset(bucket_metric, 0, sizeof(struct prometheus_metric));
   
   bucket_metric->name = strdup(metric_name);
   bucket_metric->help = strdup(temp->query_alt->columns[h_idx].description);
   bucket_metric->type = strdup("histogram");
   
   pgexporter_deque_create(false, &bucket_metric->definitions);
   
   /* Create sum metric */
   snprintf(metric_name, sizeof(metric_name), "pgexporter_%s_sum", temp->tag);
   sum_metric = malloc(sizeof(struct prometheus_metric));
   memset(sum_metric, 0, sizeof(struct prometheus_metric));
   
   sum_metric->name = strdup(metric_name);
   sum_metric->help = strdup(temp->query_alt->columns[h_idx].description);
   sum_metric->type = strdup("histogram");
   
   pgexporter_deque_create(false, &sum_metric->definitions);
   
   /* Create count metric */
   snprintf(metric_name, sizeof(metric_name), "pgexporter_%s_count", temp->tag);
   count_metric = malloc(sizeof(struct prometheus_metric));
   memset(count_metric, 0, sizeof(struct prometheus_metric));
   
   count_metric->name = strdup(metric_name);
   count_metric->help = strdup(temp->query_alt->columns[h_idx].description);
   count_metric->type = strdup("histogram");
   
   pgexporter_deque_create(false, &count_metric->definitions);

   struct tuple* current = temp->query->tuples;

   while (current)
   {
      /* Parse bucket bounds and values */
      char* bounds_str = pgexporter_get_column_by_name(names[2], temp->query, current);
      parse_list(bounds_str, bounds_arr, &n_bounds);

      char* buckets_str = pgexporter_get_column_by_name(names[3], temp->query, current);
      parse_list(buckets_str, buckets_arr, &n_buckets);

      /* Process each bucket */
      for (int i = 0; i < n_bounds; i++)
      {
         attrs = malloc(sizeof(struct prometheus_attributes));
         memset(attrs, 0, sizeof(struct prometheus_attributes));
         
         pgexporter_deque_create(false, &attrs->attributes);
         pgexporter_deque_create(false, &attrs->values);
         
         /* Add le attribute */
         attr = malloc(sizeof(struct prometheus_attribute));
         memset(attr, 0, sizeof(struct prometheus_attribute));
         
         attr->key = strdup("le");
         attr->value = strdup(bounds_arr[i]);
         
         pgexporter_deque_add(attrs->attributes, NULL, (uintptr_t)attr, ValueRef);
         
         /* Add server attribute */
         attr = malloc(sizeof(struct prometheus_attribute));
         memset(attr, 0, sizeof(struct prometheus_attribute));
         
         attr->key = strdup("server");
         attr->value = strdup(config->servers[current->server].name);
         
         pgexporter_deque_add(attrs->attributes, NULL, (uintptr_t)attr, ValueRef);
         
         /* Add other attributes */
         for (int j = 0; j < h_idx; j++)
         {
            attr = malloc(sizeof(struct prometheus_attribute));
            memset(attr, 0, sizeof(struct prometheus_attribute));
            
            attr->key = strdup(temp->query_alt->columns[j].name);
            attr->value = strdup(pgexporter_get_column(j, current));
            
            pgexporter_deque_add(attrs->attributes, NULL, (uintptr_t)attr, ValueRef);
         }
         
         /* Add value */
         val = malloc(sizeof(struct prometheus_value));
         memset(val, 0, sizeof(struct prometheus_value));
         
         val->timestamp = time(NULL);
         val->value = strdup(buckets_arr[i]);
         
         pgexporter_deque_add(attrs->values, NULL, (uintptr_t)val, ValueRef);
         
         /* Add to bucket metric */
         pgexporter_deque_add(bucket_metric->definitions, NULL, (uintptr_t)attrs, ValueRef);
      }

      /* Add +Inf bucket */
      attrs = malloc(sizeof(struct prometheus_attributes));
      memset(attrs, 0, sizeof(struct prometheus_attributes));
      
      pgexporter_deque_create(false, &attrs->attributes);
      pgexporter_deque_create(false, &attrs->values);
      
      /* Add le attribute */
      attr = malloc(sizeof(struct prometheus_attribute));
      memset(attr, 0, sizeof(struct prometheus_attribute));
      
      attr->key = strdup("le");
      attr->value = strdup("+Inf");
      
      pgexporter_deque_add(attrs->attributes, NULL, (uintptr_t)attr, ValueRef);
      
      /* Add server attribute */
      attr = malloc(sizeof(struct prometheus_attribute));
      memset(attr, 0, sizeof(struct prometheus_attribute));
      
      attr->key = strdup("server");
      attr->value = strdup(config->servers[current->server].name);
      
      pgexporter_deque_add(attrs->attributes, NULL, (uintptr_t)attr, ValueRef);
      
      /* Add other attributes */
      for (int j = 0; j < h_idx; j++)
      {
         attr = malloc(sizeof(struct prometheus_attribute));
         memset(attr, 0, sizeof(struct prometheus_attribute));
         
         attr->key = strdup(temp->query_alt->columns[j].name);
         attr->value = strdup(pgexporter_get_column(j, current));
         
         pgexporter_deque_add(attrs->attributes, NULL, (uintptr_t)attr, ValueRef);
      }
      
      /* Add value */
      val = malloc(sizeof(struct prometheus_value));
      memset(val, 0, sizeof(struct prometheus_value));
      
      val->timestamp = time(NULL);
      val->value = strdup(pgexporter_get_column_by_name(names[1], temp->query, current));
      
      pgexporter_deque_add(attrs->values, NULL, (uintptr_t)val, ValueRef);
      
      /* Add to bucket metric */
      pgexporter_deque_add(bucket_metric->definitions, NULL, (uintptr_t)attrs, ValueRef);

      /* Add sum */
      attrs = malloc(sizeof(struct prometheus_attributes));
      memset(attrs, 0, sizeof(struct prometheus_attributes));
      
      pgexporter_deque_create(false, &attrs->attributes);
      pgexporter_deque_create(false, &attrs->values);
      
      /* Add server attribute */
      attr = malloc(sizeof(struct prometheus_attribute));
      memset(attr, 0, sizeof(struct prometheus_attribute));
      
      attr->key = strdup("server");
      attr->value = strdup(config->servers[current->server].name);
      
      pgexporter_deque_add(attrs->attributes, NULL, (uintptr_t)attr, ValueRef);
      
      /* Add other attributes */
      for (int j = 0; j < h_idx; j++)
      {
         attr = malloc(sizeof(struct prometheus_attribute));
         memset(attr, 0, sizeof(struct prometheus_attribute));
         
         attr->key = strdup(temp->query_alt->columns[j].name);
         attr->value = strdup(pgexporter_get_column(j, current));
         
         pgexporter_deque_add(attrs->attributes, NULL, (uintptr_t)attr, ValueRef);
      }
      
      /* Add value */
      val = malloc(sizeof(struct prometheus_value));
      memset(val, 0, sizeof(struct prometheus_value));
      
      val->timestamp = time(NULL);
      val->value = strdup(pgexporter_get_column_by_name(names[0], temp->query, current));
      
      pgexporter_deque_add(attrs->values, NULL, (uintptr_t)val, ValueRef);
      
      /* Add to sum metric */
      pgexporter_deque_add(sum_metric->definitions, NULL, (uintptr_t)attrs, ValueRef);

      /* Add count */
      attrs = malloc(sizeof(struct prometheus_attributes));
      memset(attrs, 0, sizeof(struct prometheus_attributes));
      
      pgexporter_deque_create(false, &attrs->attributes);
      pgexporter_deque_create(false, &attrs->values);
      
      /* Add server attribute */
      attr = malloc(sizeof(struct prometheus_attribute));
      memset(attr, 0, sizeof(struct prometheus_attribute));
      
      attr->key = strdup("server");
      attr->value = strdup(config->servers[current->server].name);
      
      pgexporter_deque_add(attrs->attributes, NULL, (uintptr_t)attr, ValueRef);
      
      /* Add other attributes */
      for (int j = 0; j < h_idx; j++)
      {
         attr = malloc(sizeof(struct prometheus_attribute));
         memset(attr, 0, sizeof(struct prometheus_attribute));
         
         attr->key = strdup(temp->query_alt->columns[j].name);
         attr->value = strdup(pgexporter_get_column(j, current));
         
         pgexporter_deque_add(attrs->attributes, NULL, (uintptr_t)attr, ValueRef);
      }
      
      /* Add value */
      val = malloc(sizeof(struct prometheus_value));
      memset(val, 0, sizeof(struct prometheus_value));
      
      val->timestamp = time(NULL);
      val->value = strdup(pgexporter_get_column_by_name(names[1], temp->query, current));
      
      pgexporter_deque_add(attrs->values, NULL, (uintptr_t)val, ValueRef);
      
      /* Add to count metric */
      pgexporter_deque_add(count_metric->definitions, NULL, (uintptr_t)attrs, ValueRef);

      current = current->next;
   }

   /* Add metrics to bridge */
   pgexporter_art_insert(bridge->metrics, bucket_metric->name, (uintptr_t)bucket_metric, ValueRef);
   pgexporter_art_insert(bridge->metrics, sum_metric->name, (uintptr_t)sum_metric, ValueRef);
   pgexporter_art_insert(bridge->metrics, count_metric->name, (uintptr_t)count_metric, ValueRef);

   /* Clean up */
   for (int i = 0; i < n_bounds; i++)
   {
      free(bounds_arr[i]);
   }

   for (int i = 0; i < n_buckets; i++)
   {
      free(buckets_arr[i]);
   }

   free(names[0]);
   free(names[1]);
   free(names[2]);
   free(names[3]);
}

static int
parse_list(char* list_str, char** strs, int* n_strs)
{
   int idx = 0;
   char* data = NULL;
   char* p = NULL;
   int len = strlen(list_str);

   /**
    * If the `list_str` is `{c1,c2,c3,...,cn}`, and if the `strlen(list_str)`
    * is `x`, then it takes `x + 1` bytes in memory including the null character.
    *
    * `data` will have `list_str` without the first and last bracket (so `data` will
    * just be `c1,c2,c3,...,cn`) and thus `strlen(data)` will be `x - 2`, and
    * so will take `x - 1` bytes in memory including the null character.
    */
   data = (char*) malloc((len - 1) * sizeof(char));
   memset(data, 0, (len - 1) * sizeof(char));

   /**
    * If list_str is `{c1,c2,c3,...,cn}`, then and if `len(list_str)` is `len`
    * then this starts from `c1`, and goes for `len - 2`, so till `cn`, so the
    * `data` string becomes `c1,c2,c3,...,cn`
    */
   strncpy(data, list_str + 1, len - 2);

   p = strtok(data, ",");
   while (p)
   {
      strs[idx] = NULL;
      strs[idx] = pgexporter_append(strs[idx], p);
      idx++;
      p = strtok(NULL, ",");
   }

   *n_strs = idx;
   free(data);
   return 0;
}



static int
send_chunk(int client_fd, char* data)
{
   int status;
   char* m = NULL;
   struct message msg;

   memset(&msg, 0, sizeof(struct message));

   m = malloc(20);

   if (m == NULL)
   {
      goto error;
   }

   memset(m, 0, 20);

   sprintf(m, "%zX\r\n", strlen(data));

   m = pgexporter_vappend(m, 2,
                          data,
                          "\r\n"
                          );

   msg.kind = 0;
   msg.length = strlen(m);
   msg.data = m;

   status = pgexporter_write_message(NULL, client_fd, &msg);

   free(m);

   return status;

error:

   return MESSAGE_STATUS_ERROR;
}

static char*
get_value(char* tag, char* name, char* val)
{
   char* end = NULL;

   /* Empty to 0 */
   if (val == NULL || !strcmp(val, ""))
   {
      return "0";
   }

   /* Bool */
   if (!strcmp(val, "off") || !strcmp(val, "f") || !strcmp(val, "(disabled)"))
   {
      return "0";
   }
   else if (!strcmp(val, "on") || !strcmp(val, "t"))
   {
      return "1";
   }

   if (!strcmp(val, "NaN"))
   {
      return val;
   }

   /* long */
   strtol(val, &end, 10);
   if (*end == '\0')
   {
      return val;
   }
   errno = 0;

   /* double */
   strtod(val, &end);
   if (*end == '\0')
   {
      return val;
   }
   errno = 0;

   /* pgexporter_log_trace("get_value(%s/%s): %s", tag, name, val); */

   /* Map general strings to 1 */
   return "1";
}

static int
safe_prometheus_key_additional_length(char* key)
{
   int count = 0;
   int i = 0;

   while (key[i] != '\0')
   {
      if (key[i] == '"' || key[i] == '\\')
      {
         count++;
      }
      i++;
   }

   /* pgexporter_log_trace("key(%s): %d", key, count); */
   return count;
}

static char*
safe_prometheus_key(char* key)
{
   int i = 0;
   int j = 0;
   char* escaped = NULL;

   if (key == NULL || strlen(key) == 0)
   {
      return "";
   }

   escaped = (char*) malloc(strlen(key) + safe_prometheus_key_additional_length(key) + 1);
   while (key[i] != '\0')
   {
      if (key[i] == '.')
      {
         if (i == strlen(key) - 1)
         {
            escaped[j] = '\0';
         }
         else
         {
            escaped[j] = '_';
         }
      }
      else
      {
         if (key[i] == '"' || key[i] == '\\')
         {
            escaped[j] = '\\';
            j++;
         }
         escaped[j] = key[i];
      }

      i++;
      j++;
   }
   escaped[j] = '\0';
   return escaped;
}

static void
safe_prometheus_key_free(char* key)
{
   if (key != NULL && strlen(key) > 0)
   {
      free(key);
   }
}

/**
 * Checks if the Prometheus cache configuration setting
 * (`metrics_cache`) has a non-zero value, that means there
 * are seconds to cache the response.
 *
 * @return true if there is a cache configuration,
 *         false if no cache is active
 */
static bool
is_metrics_cache_configured(void)
{
   struct configuration* config;

   config = (struct configuration*)shmem;

   // cannot have caching if not set metrics!
   if (config->metrics == 0)
   {
      return false;
   }

   return config->metrics_cache_max_age != PGEXPORTER_PROMETHEUS_CACHE_DISABLED;
}

/**
 * Checks if the cache is still valid, and therefore can be
 * used to serve as a response.
 * A cache is considred valid if it has non-empty payload and
 * a timestamp in the future.
 *
 * @return true if the cache is still valid
 */
static bool
is_metrics_cache_valid(void)
{
   time_t now;

   struct prometheus_cache* cache;

   cache = (struct prometheus_cache*)prometheus_cache_shmem;

   if (cache->valid_until == 0 || strlen(cache->data) == 0)
   {
      return false;
   }

   now = time(NULL);
   return now <= cache->valid_until;
}

int
pgexporter_init_prometheus_cache(size_t* p_size, void** p_shmem)
{
   struct prometheus_cache* cache;
   struct configuration* config;
   size_t cache_size = 0;
   size_t struct_size = 0;

   config = (struct configuration*)shmem;

   // first of all, allocate the overall cache structure
   cache_size = metrics_cache_size_to_alloc();
   struct_size = sizeof(struct prometheus_cache);

   if (pgexporter_create_shared_memory(struct_size + cache_size, config->hugepage, (void*) &cache))
   {
      goto error;
   }

   memset(cache, 0, struct_size + cache_size);
   cache->valid_until = 0;
   cache->size = cache_size;
   atomic_init(&cache->lock, STATE_FREE);

   // success! do the memory swap
   *p_shmem = cache;
   *p_size = cache_size + struct_size;
   return 0;

error:
   // disable caching
   config->metrics_cache_max_age = config->metrics_cache_max_size = PGEXPORTER_PROMETHEUS_CACHE_DISABLED;
   pgexporter_log_error("Cannot allocate shared memory for the Prometheus cache!");
   *p_size = 0;
   *p_shmem = NULL;

   return 1;
}

/**
 * Provides the size of the cache to allocate.
 *
 * It checks if the metrics cache is configured, and
 * computers the right minimum value between the
 * user configured requested size and the default
 * cache size.
 *
 * @return the cache size to allocate
 */
static size_t
metrics_cache_size_to_alloc(void)
{
   struct configuration* config;
   size_t cache_size = 0;

   config = (struct configuration*)shmem;

   // which size to use ?
   // either the configured (i.e., requested by user) if lower than the max size
   // or the default value
   if (is_metrics_cache_configured())
   {
      cache_size = config->metrics_cache_max_size > 0
            ? MIN(config->metrics_cache_max_size, PROMETHEUS_MAX_CACHE_SIZE)
            : PROMETHEUS_DEFAULT_CACHE_SIZE;
   }

   return cache_size;
}

/**
 * Invalidates the cache.
 *
 * Requires the caller to hold the lock on the cache!
 *
 * Invalidating the cache means that the payload is zero-filled
 * and that the valid_until field is set to zero too.
 */
static void
metrics_cache_invalidate(void)
{
   struct prometheus_cache* cache;

   cache = (struct prometheus_cache*)prometheus_cache_shmem;

   memset(cache->data, 0, cache->size);
   cache->valid_until = 0;
}

/**
 * Appends data to the cache.
 *
 * Requires the caller to hold the lock on the cache!
 *
 * If the input data is empty, nothing happens.
 * The data is appended only if the cache does not overflows, that
 * means the current size of the cache plus the size of the data
 * to append does not exceed the current cache size.
 * If the cache overflows, the cache is flushed and marked
 * as invalid.
 * This makes safe to call this method along the workflow of
 * building the Prometheus response.
 *
 * @param data the string to append to the cache
 * @return true on success
 */
static bool
metrics_cache_append(char* data)
{
   int origin_length = 0;
   int append_length = 0;
   struct prometheus_cache* cache;

   cache = (struct prometheus_cache*)prometheus_cache_shmem;

   if (!is_metrics_cache_configured())
   {
      return false;
   }

   origin_length = strlen(cache->data);
   append_length = strlen(data);
   // need to append the data to the cache
   if (origin_length + append_length >= cache->size)
   {
      // cannot append new data, so invalidate cache
      pgexporter_log_debug("Cannot append %d bytes to the Prometheus cache because it will overflow the size of %d bytes (currently at %d bytes). HINT: try adjusting `metrics_cache_max_size`",
                           append_length,
                           cache->size,
                           origin_length);
      metrics_cache_invalidate();
      return false;
   }

   // append the data to the data field
   memcpy(cache->data + origin_length, data, append_length);
   cache->data[origin_length + append_length + 1] = '\0';
   return true;
}

/**
 * Finalizes the cache.
 *
 * Requires the caller to hold the lock on the cache!
 *
 * This method should be invoked when the cache is complete
 * and therefore can be served.
 *
 * @return true if the cache has a validity
 */
static bool
metrics_cache_finalize(void)
{
   struct configuration* config;
   struct prometheus_cache* cache;
   time_t now;

   cache = (struct prometheus_cache*)prometheus_cache_shmem;
   config = (struct configuration*)shmem;

   if (!is_metrics_cache_configured())
   {
      return false;
   }

   now = time(NULL);
   cache->valid_until = now + config->metrics_cache_max_age;
   return cache->valid_until > now;
}
