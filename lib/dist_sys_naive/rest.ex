defmodule DistSysNaive.Rest do
  @moduledoc """
  That's REST API. See also DistSysNaive.Sup
  """
  use Plug.Router
  plug(Plug.Logger)
  plug(:match)

  plug(Plug.Parsers,
    parsers: [:json],
    pass: ["application/json"],
    json_decoder: Jason
  )

  plug(:dispatch)

  # Call it as:
  # ```
  # curl http://localhost:8080/ && echo
  # '''
  get "/" do
    respond_answer_json(conn)
  end

  # Call it as
  # ```
  # curl -X PUT http://localhost:8080/ -H 'Content-Type: application/json' -d '{"answer":"great"}' && echo
  # '''
  put "/" do
    %{"answer" => answer} = conn.body_params
    DistSysNaive.Node.propose_answer(answer)
    respond_answer_json(conn)
  end

  # Fallback handler when there was no match
  match _ do
    send_resp(conn, 404, "Not Found")
  end

  defp respond_answer_json(conn) do
    {:ok, answer} = DistSysNaive.Node.get_answer()
    send_resp(conn, 200, Jason.encode!(%{"answer" => answer}))
  end
end
