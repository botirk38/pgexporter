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
#include <openssl/crypto.h>
#include <pgexporter.h>
#include <art.h>
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
 * ART-based metric value with timestamp
 */
typedef struct prometheus_metric_value
{
   time_t timestamp;
   char* value;
   char* help;
   char* type;
   int sort_type;
} prometheus_metric_value_t;

/**
 * ART-based metrics container for each category
 */
typedef struct prometheus_metrics_container
{
   struct art* general_metrics;
   struct art* server_metrics;
   struct art* version_metrics;
   struct art* uptime_metrics;
   struct art* primary_metrics;
   struct art* core_metrics;
   struct art* extension_metrics;
   struct art* extension_list_metrics;
   struct art* settings_metrics;
   struct art* custom_metrics;
} prometheus_metrics_container_t;

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
static int badrequest_page(SSL* client_ssl, int client_fd);
static int unknown_page(SSL* client_ssl, int client_fd);
static int home_page(SSL* client_ssl, int client_fd);
static int metrics_page(SSL* client_ssl, int client_fd);
static int bad_request(SSL* client_ssl, int client_fd);
static int redirect_page(SSL* client_ssl, int client_fd, char* path);

static bool collector_pass(const char* collector);

// ART-based metric handling functions
static int create_metrics_container(prometheus_metrics_container_t** container);
static void destroy_metrics_container(prometheus_metrics_container_t* container);
static int add_metric_to_art(struct art* art_tree, char* key, char* value, char* help, char* type, time_t timestamp, int sort_type);
static void output_art_metrics(SSL* client_ssl, int client_fd, struct art* art_tree, char* category_name);
static void output_all_metrics(SSL* client_ssl, int client_fd, prometheus_metrics_container_t* container);
static void prometheus_metric_value_destroy_cb(uintptr_t data);
static char* prometheus_metric_value_string_cb(uintptr_t data, int32_t format, char* tag, int indent);

static void general_information(prometheus_metrics_container_t* container);
static void core_information(prometheus_metrics_container_t* container);
static void extension_information(prometheus_metrics_container_t* container);
static void extension_list_information(prometheus_metrics_container_t* container);
static void extension_function(char* function, int input, char* description, char* type, prometheus_metrics_container_t* container);
static void server_information(prometheus_metrics_container_t* container);
static void version_information(prometheus_metrics_container_t* container);
static void uptime_information(prometheus_metrics_container_t* container);
static void primary_information(prometheus_metrics_container_t* container);
static void settings_information(prometheus_metrics_container_t* container);
static void custom_metrics(prometheus_metrics_container_t* container);

static int send_chunk(SSL* client_ssl, int client_fd, char* data);

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
pgexporter_prometheus(SSL* client_ssl, int client_fd)
{
   int status;
   int page;
   struct message* msg = NULL;
   struct configuration* config;

   pgexporter_start_logging();
   pgexporter_memory_init();

   config = (struct configuration*)shmem;
   if (client_ssl)
   {
      char buffer[5] = {0};

      recv(client_fd, buffer, 5, MSG_PEEK);

      if ((unsigned char)buffer[0] == 0x16 || (unsigned char)buffer[0] == 0x80) // SSL/TLS request
      {
         if (SSL_accept(client_ssl) <= 0)
         {
            pgexporter_log_error("Failed to accept SSL connection");
            goto error;
         }
      }
      else
      {
         char* path = "/";
         char* base_url = NULL;

         if (pgexporter_read_timeout_message(NULL, client_fd, config->authentication_timeout, &msg) != MESSAGE_STATUS_OK)
         {
            pgexporter_log_error("Failed to read message");
            goto error;
         }

         char* path_start = strstr(msg->data, " ");
         if (path_start)
         {
            path_start++;
            char* path_end = strstr(path_start, " ");
            if (path_end)
            {
               *path_end = '\0';
               path = path_start;
            }
         }

         base_url = pgexporter_format_and_append(base_url, "https://localhost:%d%s", config->metrics, path);

         if (redirect_page(NULL, client_fd, base_url) != MESSAGE_STATUS_OK)
         {
            pgexporter_log_error("Failed to redirect to: %s", base_url);
            free(base_url);
            goto error;
         }

         pgexporter_close_ssl(client_ssl);
         pgexporter_disconnect(client_fd);

         pgexporter_memory_destroy();
         pgexporter_stop_logging();

         free(base_url);

         exit(0);
      }
   }
   status = pgexporter_read_timeout_message(client_ssl, client_fd, config->authentication_timeout, &msg);

   if (status != MESSAGE_STATUS_OK)
   {
      goto error;
   }

   page = resolve_page(msg);

   if (page == PAGE_HOME)
   {
      home_page(client_ssl, client_fd);
   }
   else if (page == PAGE_METRICS)
   {
      metrics_page(client_ssl, client_fd);
   }
   else if (page == PAGE_UNKNOWN)
   {
      unknown_page(client_ssl, client_fd);
   }
   else
   {
      bad_request(client_ssl, client_fd);
   }

   pgexporter_close_ssl(client_ssl);
   pgexporter_disconnect(client_fd);

   pgexporter_memory_destroy();
   pgexporter_stop_logging();

   exit(0);

error:

   badrequest_page(client_ssl, client_fd);

   pgexporter_close_ssl(client_ssl);
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
redirect_page(SSL* client_ssl, int client_fd, char* path)
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

   data = pgexporter_append(data, "HTTP/1.1 301 Moved Permanently\r\n");
   data = pgexporter_append(data, "Location: ");
   data = pgexporter_append(data, path);
   data = pgexporter_append(data, "\r\n");
   data = pgexporter_append(data, "Date: ");
   data = pgexporter_append(data, &time_buf[0]);
   data = pgexporter_append(data, "\r\n");
   data = pgexporter_append(data, "Content-Length: 0\r\n");
   data = pgexporter_append(data, "Connection: close\r\n");
   data = pgexporter_append(data, "\r\n");

   msg.kind = 0;
   msg.length = strlen(data);
   msg.data = data;

   status = pgexporter_write_message(client_ssl, client_fd, &msg);

   free(data);

   return status;
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
badrequest_page(SSL* client_ssl, int client_fd)
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

   status = pgexporter_write_message(client_ssl, client_fd, &msg);

   free(data);

   return status;
}

static int
unknown_page(SSL* client_ssl, int client_fd)
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

   status = pgexporter_write_message(client_ssl, client_fd, &msg);

   free(data);

   return status;
}

static int
home_page(SSL* client_ssl, int client_fd)
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

   status = pgexporter_write_message(client_ssl, client_fd, &msg);
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

   send_chunk(client_ssl, client_fd, data);
   free(data);
   data = NULL;

   data = pgexporter_vappend(data, 4,
                             "  <li>pgexporter_logging_info</li>\n",
                             "  <li>pgexporter_logging_warn</li>\n",
                             "  <li>pgexporter_logging_error</li>\n",
                             "  <li>pgexporter_logging_fatal</li>\n"
                             );

   send_chunk(client_ssl, client_fd, data);
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

   send_chunk(client_ssl, client_fd, data);
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

   send_chunk(client_ssl, client_fd, data);
   free(data);
   data = NULL;

   return 0;

error:

   free(data);

   return 1;
}

static int
metrics_page(SSL* client_ssl, int client_fd)
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

         status = pgexporter_write_message(client_ssl, client_fd, &msg);
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

         status = pgexporter_write_message(client_ssl, client_fd, &msg);
         if (status != MESSAGE_STATUS_OK)
         {
            goto error;
         }

         free(data);
         data = NULL;

         pgexporter_open_connections();

         /* ART-based Metric Collection */
         prometheus_metrics_container_t* container = NULL;

         if (create_metrics_container(&container) == 0)
         {
            /* General Metric Collector */
            general_information(container);
            core_information(container);
            server_information(container);
            version_information(container);
            uptime_information(container);
            primary_information(container);
            settings_information(container);
            extension_information(container);
            extension_list_information(container);

            custom_metrics(container);

            output_all_metrics(client_ssl, client_fd, container);
            destroy_metrics_container(container);
         }

         pgexporter_close_connections();

         /* Footer */
         data = pgexporter_append(data, "0\r\n\r\n");

         msg.kind = 0;
         msg.length = strlen(data);
         msg.data = data;

         status = pgexporter_write_message(client_ssl, client_fd, &msg);
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

   free(data);

   return 1;
}

static int
bad_request(SSL* client_ssl, int client_fd)
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

   status = pgexporter_write_message(client_ssl, client_fd, &msg);

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
general_information(prometheus_metrics_container_t* container)
{
   time_t current_time = time(NULL);
   struct configuration* config = (struct configuration*)shmem;
   char value_buffer[256];

   if (container == NULL || container->general_metrics == NULL)
   {
      return;
   }

   add_metric_to_art(container->general_metrics,
                     "pgexporter_state",
                     "1",
                     "The state of pgexporter",
                     "gauge",
                     current_time,
                     SORT_NAME);

   snprintf(value_buffer, sizeof(value_buffer), "%lu", atomic_load(&config->logging_info));
   add_metric_to_art(container->general_metrics,
                     "pgexporter_logging_info",
                     value_buffer,
                     "The number of INFO logging statements",
                     "gauge",
                     current_time,
                     SORT_NAME);

   snprintf(value_buffer, sizeof(value_buffer), "%lu", atomic_load(&config->logging_warn));
   add_metric_to_art(container->general_metrics,
                     "pgexporter_logging_warn",
                     value_buffer,
                     "The number of WARN logging statements",
                     "gauge",
                     current_time,
                     SORT_NAME);

   snprintf(value_buffer, sizeof(value_buffer), "%lu", atomic_load(&config->logging_error));
   add_metric_to_art(container->general_metrics,
                     "pgexporter_logging_error",
                     value_buffer,
                     "The number of ERROR logging statements",
                     "gauge",
                     current_time,
                     SORT_NAME);

   snprintf(value_buffer, sizeof(value_buffer), "%lu", atomic_load(&config->logging_fatal));
   add_metric_to_art(container->general_metrics,
                     "pgexporter_logging_fatal",
                     value_buffer,
                     "The number of FATAL logging statements",
                     "gauge",
                     current_time,
                     SORT_NAME);
}

static void
server_information(prometheus_metrics_container_t* container)
{
   time_t current_time = time(NULL);
   struct configuration* config = (struct configuration*)shmem;
   char metric_name[512];
   char value_buffer[256];

   if (container == NULL || container->server_metrics == NULL)
   {
      return;
   }

   for (int server = 0; server < config->number_of_servers; server++)
   {
      snprintf(metric_name, sizeof(metric_name), "pgexporter_postgresql_active{server=\"%s\"}", config->servers[server].name);

      if (config->servers[server].fd != -1)
      {
         strcpy(value_buffer, "1");
      }
      else
      {
         strcpy(value_buffer, "0");
      }

      add_metric_to_art(container->server_metrics,
                        metric_name,
                        value_buffer,
                        "The state of PostgreSQL",
                        "gauge",
                        current_time,
                        SORT_NAME);
   }
}

static void
version_information(prometheus_metrics_container_t* container)
{
   int ret;
   int server;
   time_t current_time = time(NULL);
   char* safe_key1 = NULL;
   char* safe_key2 = NULL;
   char metric_name[512];
   struct query* all = NULL;
   struct query* query = NULL;
   struct tuple* current = NULL;
   struct configuration* config;

   if (container == NULL || container->version_metrics == NULL)
   {
      return;
   }

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
         server = 0;

         while (current != NULL)
         {
            safe_key1 = safe_prometheus_key(pgexporter_get_column(0, current));
            safe_key2 = safe_prometheus_key(pgexporter_get_column(1, current));

            snprintf(metric_name, sizeof(metric_name),
                     "pgexporter_postgresql_version{server=\"%s\",version=\"%s\",minor_version=\"%s\"}",
                     config->servers[server].name, safe_key1, safe_key2);

            add_metric_to_art(container->version_metrics,
                              metric_name,
                              "1",
                              "The PostgreSQL version",
                              "gauge",
                              current_time,
                              SORT_NAME);

            safe_prometheus_key_free(safe_key1);
            safe_prometheus_key_free(safe_key2);

            server++;
            current = current->next;
         }
      }
   }

   pgexporter_free_query(all);
}

static void
uptime_information(prometheus_metrics_container_t* container)
{
   int ret;
   int server;
   time_t current_time = time(NULL);
   char* safe_key = NULL;
   char metric_name[512];
   struct query* all = NULL;
   struct query* query = NULL;
   struct tuple* current = NULL;
   struct configuration* config;

   if (container == NULL || container->uptime_metrics == NULL)
   {
      return;
   }

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
         server = 0;

         while (current != NULL)
         {
            safe_key = safe_prometheus_key(pgexporter_get_column(0, current));

            snprintf(metric_name, sizeof(metric_name),
                     "pgexporter_postgresql_uptime{server=\"%s\"}",
                     config->servers[server].name);

            add_metric_to_art(container->uptime_metrics,
                              metric_name,
                              safe_key,
                              "The PostgreSQL uptime in seconds",
                              "gauge",
                              current_time,
                              SORT_NAME);

            safe_prometheus_key_free(safe_key);

            server++;
            current = current->next;
         }
      }
   }

   pgexporter_free_query(all);
}

static void
primary_information(prometheus_metrics_container_t* container)
{
   int ret;
   int server;
   time_t current_time = time(NULL);
   char metric_name[512];
   struct query* all = NULL;
   struct query* query = NULL;
   struct tuple* current = NULL;
   struct configuration* config;

   if (container == NULL || container->primary_metrics == NULL)
   {
      return;
   }

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
         server = 0;

         while (current != NULL)
         {
            snprintf(metric_name, sizeof(metric_name),
                     "pgexporter_postgresql_primary{server=\"%s\"}",
                     config->servers[server].name);

            const char* value = "0";
            if (!strcmp("t", pgexporter_get_column(0, current)))
            {
               value = "1";
            }

            add_metric_to_art(container->primary_metrics,
                              metric_name,
                              (char*)value,
                              "Is the PostgreSQL instance the primary",
                              "gauge",
                              current_time,
                              SORT_NAME);

            server++;
            current = current->next;
         }
      }
   }

   pgexporter_free_query(all);
}

static void
core_information(prometheus_metrics_container_t* container)
{
   time_t current_time = time(NULL);
   char metric_name[512];

   if (container == NULL || container->core_metrics == NULL)
   {
      return;
   }

   snprintf(metric_name, sizeof(metric_name), "pgexporter_version{pgexporter_version=\"%s\"}", VERSION);

   add_metric_to_art(container->core_metrics,
                     metric_name,
                     "1",
                     "The pgexporter version",
                     "counter",
                     current_time,
                     SORT_NAME);
}

static void
extension_information(prometheus_metrics_container_t* container)
{
   bool cont = true;
   struct query* query = NULL;
   struct tuple* tuple = NULL;
   struct configuration* config;

   if (container == NULL || container->extension_metrics == NULL)
   {
      return;
   }

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
                     extension_function(tuple->data[0], false, tuple->data[2], tuple->data[3], container);
                  }
               }
               else
               {
                  if (strcmp(tuple->data[0], "pgexporter_is_supported"))
                  {
                     extension_function(tuple->data[0], INPUT_DATA, tuple->data[2], tuple->data[3], container);
                     extension_function(tuple->data[0], INPUT_WAL, tuple->data[2], tuple->data[3], container);
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
extension_list_information(prometheus_metrics_container_t* container)
{
   time_t current_time = time(NULL);
   char* safe_key1 = NULL;
   char* safe_key2 = NULL;
   char* safe_key3 = NULL;
   char metric_name[512];
   struct configuration* config;

   if (container == NULL || container->extension_list_metrics == NULL)
   {
      return;
   }

   config = (struct configuration*)shmem;

   if (!collector_pass("extensions_list"))
   {
      return;
   }

   for (int server = 0; server < config->number_of_servers; server++)
   {
      if (config->servers[server].fd != -1)
      {
         for (int i = 0; i < config->servers[server].number_of_extensions; i++)
         {
            safe_key1 = safe_prometheus_key(config->servers[server].extensions[i].name);
            safe_key2 = safe_prometheus_key(config->servers[server].extensions[i].installed_version);
            safe_key3 = safe_prometheus_key(config->servers[server].extensions[i].comment);

            snprintf(metric_name, sizeof(metric_name),
                     "pgexporter_postgresql_extension_info{server=\"%s\",extension=\"%s\",version=\"%s\",comment=\"%s\"}",
                     config->servers[server].name, safe_key1, safe_key2, safe_key3);

            add_metric_to_art(container->extension_list_metrics,
                              metric_name,
                              "1",
                              "Information about installed PostgreSQL extensions",
                              "gauge",
                              current_time,
                              SORT_NAME);

            safe_prometheus_key_free(safe_key1);
            safe_prometheus_key_free(safe_key2);
            safe_prometheus_key_free(safe_key3);
         }
      }
   }
}

static void
extension_function(char* function, int input, char* description, char* type, prometheus_metrics_container_t* container)
{
   time_t current_time = time(NULL);
   char metric_name[512];
   char* sql = NULL;
   struct query* query = NULL;
   struct tuple* tuple = NULL;
   struct configuration* config;

   if (container == NULL || container->extension_metrics == NULL)
   {
      return;
   }

   config = (struct configuration*)shmem;

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
            char base_metric_name[256];
            strcpy(base_metric_name, function);

            if (input == INPUT_DATA)
            {
               strcat(base_metric_name, "_data");
            }
            else if (input == INPUT_WAL)
            {
               strcat(base_metric_name, "_wal");
            }

            if (input == INPUT_NO)
            {
               snprintf(metric_name, sizeof(metric_name), "%s{server=\"%s\"}",
                        base_metric_name, config->servers[server].name);

               add_metric_to_art(container->extension_metrics,
                                 metric_name,
                                 "1",
                                 description,
                                 type,
                                 current_time,
                                 SORT_NAME);
            }
            else
            {
               const char* location = "";
               if (input == INPUT_DATA)
               {
                  location = config->servers[server].data;
               }
               else if (input == INPUT_WAL)
               {
                  location = config->servers[server].wal;
               }

               snprintf(metric_name, sizeof(metric_name), "%s{server=\"%s\",location=\"%s\"}",
                        base_metric_name, config->servers[server].name, location);

               add_metric_to_art(container->extension_metrics,
                                 metric_name,
                                 tuple->data[0],
                                 description,
                                 type,
                                 current_time,
                                 SORT_NAME);
            }

            tuple = tuple->next;
         }

         free(sql);
         sql = NULL;

         pgexporter_free_query(query);
         query = NULL;
      }
   }
}

static void
settings_information(prometheus_metrics_container_t* container)
{
   int ret;
   time_t current_time = time(NULL);
   char* safe_key = NULL;
   char metric_name[512];
   struct query* all = NULL;
   struct query* query = NULL;
   struct tuple* current = NULL;
   struct configuration* config;

   if (container == NULL || container->settings_metrics == NULL)
   {
      return;
   }

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

         snprintf(metric_name, sizeof(metric_name), "pgexporter_%s_%s", all->tag, safe_key);

         add_metric_to_art(container->settings_metrics,
                           metric_name,
                           pgexporter_get_column(1, current),
                           pgexporter_get_column(2, current),
                           "gauge",
                           current_time,
                           SORT_DATA0);

         safe_prometheus_key_free(safe_key);

         current = current->next;
      }
   }

   pgexporter_free_query(all);
}

static void
custom_metrics(prometheus_metrics_container_t* container)
{
   struct configuration* config = NULL;
   time_t current_time = time(NULL);

   if (container == NULL || container->custom_metrics == NULL)
   {
      return;
   }

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

   /* Process queries and add to ART */
   temp = q_list;
   while (temp)
   {
      if (!temp->error && temp->query != NULL && temp->query->tuples != NULL)
      {
         struct tuple* current_tuple = temp->query->tuples;
         while (current_tuple != NULL)
         {
            char metric_name[512];

            if (temp->query->number_of_columns > 0)
            {
               // For custom metrics, use the tag as the base metric name
               snprintf(metric_name, sizeof(metric_name), "pgexporter_%s", temp->tag);

               // Use the first column as the value
               add_metric_to_art(container->custom_metrics,
                                 metric_name,
                                 pgexporter_get_column(0, current_tuple),
                                 "Custom metric",
                                 "gauge",
                                 current_time,
                                 temp->sort_type);
            }

            current_tuple = current_tuple->next;
         }
      }
      temp = temp->next;
   }

   // Clean up
   temp = q_list;
   query_list_t* last = NULL;
   while (temp)
   {
      pgexporter_free_query(temp->query);
      last = temp;
      temp = temp->next;
      free(last);
   }
   q_list = NULL;
}

static int
send_chunk(SSL* client_ssl, int client_fd, char* data)
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

   status = pgexporter_write_message(client_ssl, client_fd, &msg);

   free(m);

   return status;

error:

   return MESSAGE_STATUS_ERROR;
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
   size_t i = 0;
   size_t j = 0;
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
   size_t origin_length = 0;
   size_t append_length = 0;
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

/**
 * ART-based metric value destructor callback
 */
static void
prometheus_metric_value_destroy_cb(uintptr_t data)
{
   prometheus_metric_value_t* metric = (prometheus_metric_value_t*)data;
   if (metric != NULL)
   {
      free(metric->value);
      free(metric->help);
      free(metric->type);
      free(metric);
   }
}

/**
 * ART-based metric value to string callback
 */
static char*
prometheus_metric_value_string_cb(uintptr_t data, int32_t format, char* tag, int indent)
{
   prometheus_metric_value_t* metric = (prometheus_metric_value_t*)data;
   char* result = NULL;

   (void)format;
   (void)tag;
   (void)indent;

   if (metric != NULL)
   {
      result = pgexporter_append(result, metric->value);
   }

   return result;
}

/**
 * Create metrics container with ART for each category
 */
static int
create_metrics_container(prometheus_metrics_container_t** container)
{
   prometheus_metrics_container_t* c = NULL;

   if (container == NULL)
   {
      return 1;
   }

   c = malloc(sizeof(prometheus_metrics_container_t));
   if (c == NULL)
   {
      return 1;
   }

   memset(c, 0, sizeof(prometheus_metrics_container_t));

   // Create ART for each category
   if (pgexporter_art_create(&c->general_metrics) ||
       pgexporter_art_create(&c->server_metrics) ||
       pgexporter_art_create(&c->version_metrics) ||
       pgexporter_art_create(&c->uptime_metrics) ||
       pgexporter_art_create(&c->primary_metrics) ||
       pgexporter_art_create(&c->core_metrics) ||
       pgexporter_art_create(&c->extension_metrics) ||
       pgexporter_art_create(&c->extension_list_metrics) ||
       pgexporter_art_create(&c->settings_metrics) ||
       pgexporter_art_create(&c->custom_metrics))
   {
      destroy_metrics_container(c);
      return 1;
   }

   *container = c;
   return 0;
}

/**
 * Destroy metrics container and all ART structures
 */
static void
destroy_metrics_container(prometheus_metrics_container_t* container)
{
   if (container == NULL)
   {
      return;
   }

   pgexporter_art_destroy(container->general_metrics);
   pgexporter_art_destroy(container->server_metrics);
   pgexporter_art_destroy(container->version_metrics);
   pgexporter_art_destroy(container->uptime_metrics);
   pgexporter_art_destroy(container->primary_metrics);
   pgexporter_art_destroy(container->core_metrics);
   pgexporter_art_destroy(container->extension_metrics);
   pgexporter_art_destroy(container->extension_list_metrics);
   pgexporter_art_destroy(container->settings_metrics);
   pgexporter_art_destroy(container->custom_metrics);

   free(container);
}

/**
 * Add metric to ART with timestamp
 */
static int
add_metric_to_art(struct art* art_tree, char* key, char* value, char* help, char* type, time_t timestamp, int sort_type)
{
   prometheus_metric_value_t* metric_value = NULL;
   struct value_config vc = {.destroy_data = &prometheus_metric_value_destroy_cb,
                             .to_string = &prometheus_metric_value_string_cb};

   if (art_tree == NULL || key == NULL || value == NULL)
   {
      return 1;
   }

   // Create metric value with timestamp
   metric_value = malloc(sizeof(prometheus_metric_value_t));
   if (metric_value == NULL)
   {
      return 1;
   }

   metric_value->timestamp = timestamp;
   metric_value->value = pgexporter_append(NULL, value);
   metric_value->help = help ? pgexporter_append(NULL, help) : NULL;
   metric_value->type = type ? pgexporter_append(NULL, type) : pgexporter_append(NULL, "gauge");
   metric_value->sort_type = sort_type;

   // Insert into ART (will replace if key exists)
   if (pgexporter_art_insert_with_config(art_tree, key, (uintptr_t)metric_value, &vc))
   {
      free(metric_value->value);
      free(metric_value->help);
      free(metric_value->type);
      free(metric_value);
      return 1;
   }

   return 0;
}

/**
 * Output metrics from ART in sorted order
 */
static void
output_art_metrics(SSL* client_ssl, int client_fd, struct art* art_tree, char* category_name)
{
   struct art_iterator* iter = NULL;
   char* data = NULL;

   (void)category_name;

   if (art_tree == NULL || pgexporter_art_iterator_create(art_tree, &iter))
   {
      return;
   }

   while (pgexporter_art_iterator_next(iter))
   {
      prometheus_metric_value_t* metric = (prometheus_metric_value_t*)iter->value->data;
      char* metric_key = iter->key;

      // Output HELP line
      if (metric->help != NULL)
      {
         data = pgexporter_append(data, "# HELP ");
         data = pgexporter_append(data, metric_key);
         data = pgexporter_append_char(data, ' ');
         data = pgexporter_append(data, metric->help);
         data = pgexporter_append_char(data, '\n');
      }

      // Output TYPE line
      data = pgexporter_append(data, "# TYPE ");
      data = pgexporter_append(data, metric_key);
      data = pgexporter_append_char(data, ' ');
      data = pgexporter_append(data, metric->type);
      data = pgexporter_append_char(data, '\n');

      // Output metric value with timestamp
      data = pgexporter_append(data, metric_key);
      data = pgexporter_append_char(data, ' ');
      data = pgexporter_append(data, metric->value);
      data = pgexporter_append_char(data, ' ');

      // Add timestamp in milliseconds
      char timestamp_str[32];
      snprintf(timestamp_str, sizeof(timestamp_str), "%ld000", metric->timestamp);
      data = pgexporter_append(data, timestamp_str);
      data = pgexporter_append_char(data, '\n');

      // Send chunk and cache
      send_chunk(client_ssl, client_fd, data);
      metrics_cache_append(data);

      free(data);
      data = NULL;
   }

   pgexporter_art_iterator_destroy(iter);
}

/**
 * Output all metrics from container in category order
 */
static void
output_all_metrics(SSL* client_ssl, int client_fd, prometheus_metrics_container_t* container)
{
   if (container == NULL)
   {
      return;
   }

   // Output metrics from each category ART in sorted order
   output_art_metrics(client_ssl, client_fd, container->general_metrics, "general");
   output_art_metrics(client_ssl, client_fd, container->server_metrics, "server");
   output_art_metrics(client_ssl, client_fd, container->version_metrics, "version");
   output_art_metrics(client_ssl, client_fd, container->uptime_metrics, "uptime");
   output_art_metrics(client_ssl, client_fd, container->primary_metrics, "primary");
   output_art_metrics(client_ssl, client_fd, container->core_metrics, "core");
   output_art_metrics(client_ssl, client_fd, container->extension_metrics, "extension");
   output_art_metrics(client_ssl, client_fd, container->extension_list_metrics, "extension_list");
   output_art_metrics(client_ssl, client_fd, container->settings_metrics, "settings");
   output_art_metrics(client_ssl, client_fd, container->custom_metrics, "custom");
}
