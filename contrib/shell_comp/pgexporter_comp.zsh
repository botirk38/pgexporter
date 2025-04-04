#compdef _pgexporter_cli pgexporter-cli
#compdef _pgexporter_admin pgexporter-admin


function _pgexporter_cli()
{
    local line
    _arguments -C \
               "1: :(ping shutdown status conf clear)" \
               "*::arg:->args"
    case $line[1] in
        status)
            _pgexporter_cli_status
            ;;
        conf)
            _pgexporter_cli_conf
            ;;
        clear)
            _pgexporter_cli_clear
            ;;
    esac
}

function _pgexporter_cli_status()
{
    _arguments -C \
               "1: :(details)" \
               "*::arg:->args"
}

function _pgexporter_cli_conf()
{
    _arguments -C \
               "1: :(reload)" \
               "*::arg:->args"
}

function _pgexporter_cli_clear()
{
    _arguments -C \
               "1: :(prometheus)" \
               "*::arg:->args"
}

function _pgexporter_admin()
{
   local line
    _arguments -C \
               "1: :(master-key user)" \
               "*::arg:->args"

    case $line[1] in
        user)
            _pgexporter_admin_user
            ;;
    esac
}

function _pgexporter_admin_user()
{
    _arguments -C \
               "1: :(add del edit ls)" \
               "*::arg:->args"
}
