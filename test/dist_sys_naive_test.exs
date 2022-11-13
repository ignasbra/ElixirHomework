defmodule DistSysNaiveTest do
  use ExUnit.Case

  test "greets the world" do
    assert DistSysNaive.hello() == :world
  end

  test "cluster" do
    :ok = LocalCluster.start()
    nodes = LocalCluster.start_nodes("dsn-", 2)
    [n1, n2] = nodes
    assert Node.make_move(:player1, 1) == :pong

    DistSysNaive.Node.propose_answer(n1, "some")
    Process.sleep(100)
    {:ok, "some"} = DistSysNaive.Node.get_answer(n2)

    :ok = LocalCluster.stop()
  end
end
