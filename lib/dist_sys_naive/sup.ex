defmodule DistSysNaive.Sup do
  def start_link() do
    # We only start HTTP, if DSN_PORT environment variable is set.
    http =
      case System.get_env("DSN_PORT") do
        nil ->
          []

        http_port ->
          http_opts = [port: String.to_integer(http_port)]
          [{Plug.Cowboy, scheme: :http, plug: DistSysNaive.Rest, options: http_opts}]
      end

    children =
      [
        %{id: DistSysNaive.Node, start: {DistSysNaive.Node, :start_link, []}}
      ] ++ http

    Supervisor.start_link(children, strategy: :one_for_all)
  end
end
