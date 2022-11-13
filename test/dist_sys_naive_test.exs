defmodule DistSysNaiveTest do
  use ExUnit.Case

  test "winner" do
    :ok = LocalCluster.start()
    nodes = LocalCluster.start_nodes("dsn-", 2)
    [n1, n2] = nodes

    assert DistSysNaive.Node.make_move(:player1, 0) == {:ok, [ "X", " ", " ",
                                                  " ", " ", " ",
                                                  " ", " ", " " ]}

    assert DistSysNaive.Node.make_move(:player2, 3) == {:ok, [ "X", " ", " ",
                                                  "O", " ", " ",
                                                  " ", " ", " " ]}

    assert DistSysNaive.Node.make_move(:player1, 1) == {:ok, [ "X", "X", " ",
                                                  "O", " ", " ",
                                                  " ", " ", " " ]}

    assert DistSysNaive.Node.make_move(:player2, 4) == {:ok, [ "X", "X", " ",
                                                  "O", "O", " ",
                                                  " ", " ", " " ]}

    assert DistSysNaive.Node.make_move(:player1, 2) == {:ok, [ "X", "X", "X",
                                                  "O", "O", " ",
                                                  " ", " ", " " ]}

    Process.sleep(100)

    {:ok, [ "X", "X", "X", "O", "O", " ", " ", " ", " " ]} = DistSysNaive.Node.get_board(n2)
    {:ok, [ "X", "X", "X", "O", "O", " ", " ", " ", " " ]} = DistSysNaive.Node.get_board(n1)
    {status, result} = DistSysNaive.Node.get_board(n1)
    {:ok, "X"} = DistSysNaive.Node.get_winner()

    :ok = LocalCluster.stop()
  end
end
