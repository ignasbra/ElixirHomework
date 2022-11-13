defmodule DistSysNaive.App do
  use Application

  def start(_start_mode, _start_arg) do
    # Add the local node to the specified Scopes.
    # Syn (short for synonym) is a scalable global Process Registry and Process Group manager for Erlang and Elixir, able to automatically manage dynamic clusters (addition / removal of nodes) and to recover from net splits.
    :ok = :syn.add_node_to_scopes([:dist_sys_naive])
    DistSysNaive.Sup.start_link()
  end
end
