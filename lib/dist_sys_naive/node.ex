defmodule DistSysNaive.Node do
  require Logger
  use GenServer

  ### Interface
  def start_link(), do: GenServer.start_link(__MODULE__, {}, name: __MODULE__)

  def get_players(), do: GenServer.call(__MODULE__, :get_players)
  def put_player(number, name), do: GenServer.cast(__MODULE__, {:put_player, number, name, 1})
  def put_player(node, number, name), do: GenServer.cast({__MODULE__, node}, {:put_player, number, name, 1})

  def get_board(), do: GenServer.call(__MODULE__, :get_board)
  def get_board(node), do: GenServer.call({__MODULE__, node}, :get_board)

  def get_winner(), do: GenServer.call(__MODULE__, :get_winner)
  def get_winner(node), do: GenServer.call({__MODULE__, node}, :get_winner)

  def make_move(number, move) do
    GenServer.cast(__MODULE__, {:make_move, number, move, 1})
    {status, payload} = get_board()
  end


  ### Callbacks
  defmodule State do
    @enforce_keys [:player1, :player2]
    defstruct [player1: nil, player2: nil, board: [nil, nil, nil, nil, nil, nil, nil, nil, nil], scalarClock: 1]
  end

  @impl GenServer
  def init(_arg) do

    #A global Process Group is a named group which contains many processes, possibly running on different nodes. With the group Name, you can retrieve on any cluster node the list of these processes, or publish a message to all of them. This mechanism allows for Publish / Subscribe patterns.

    :ok = :syn.join(:dist_sys_naive, :node, self()) ## Į procesų registro grupę užregistruoja save.

    state = %State{player1: "Unknown", player2: "Unknown", }
    Logger.debug("Started")
    {:ok, state}
  end

  @impl GenServer
  def handle_call(:get_board, _from, state = %State{board: result}) do

    result = Enum.map(result, fn x ->
      case x do
        nil -> " "
        _ -> x
      end
    end)

    IO.puts(" #{Enum.at(result, 0)} | #{Enum.at(result, 1)} |  #{Enum.at(result, 2)} ")
    IO.puts("-----------")
    IO.puts(" #{Enum.at(result, 3)} | #{Enum.at(result, 4)} | #{Enum.at(result, 5)} ")
    IO.puts("-----------")
    IO.puts(" #{Enum.at(result, 6)} | #{Enum.at(result, 7)} | #{Enum.at(result, 8)} ")
    IO.puts("Clock = #{state.scalarClock}")

    {:reply, {:ok, result}, state}
  end

  @impl GenServer
  def handle_call(:get_players, _from, state = %State{player1: player1, player2: player2}) do
    {:reply, {:ok, player1, player2}, state}
  end

  @impl GenServer
  def handle_call(:get_winner, _from, state = %State{board: board}) do

    case board do
      [s, s, s,
      _, _, _,
      _, _, _] when s != " " -> {:reply, {:ok, s}, state}

      [_, _, _,
       s, s, s,
       _, _, _] when s != " "-> {:reply, {:ok, s}, state}

      [_, _, _,
       _, _, _,
       s, s, s] when s != " " -> {:reply, {:ok, s}, state}

      [s, _, _,
       s, _, _,
       s, _, _] when s != " "-> {:reply, {:ok, s}, state}

      [_, s, _,
       _, s, _,
       _, s, _] when s != " " -> {:reply, {:ok, s}, state}

      [_, _, s,
       _, _, s,
       _, _, s] when s != " " -> {:reply, {:ok, s}, state}

      [s, _, _,
       _, s, _,
       _, _, s] when s != " " -> {:reply, {:ok, s}, state}

      [_, _, s,
       _, s, _,
       s, _, _] when s != " " -> {:reply, {:ok, s}, state}

       _ -> "none"
    end
  end

  @impl GenServer
  def handle_cast({:put_player, number, name, ttl}, state) do
    self = self()
    # syn.members Returns the list of all members for GroupName in the specified Scope.
    # Kiekvieną procesų grupėje esantį pid'ą išskyrus save įsikelti į members kintamąjį.
    members = for {pid, _} <- :syn.members(:dist_sys_naive, :node), pid != self, do: pid
    Logger.debug("Put player: #{inspect(number)} #{inspect(name)}, ttl=#{ttl}, members=#{inspect(members)}")

    ## Kiekvienam kitam memberiui perduoti atsakymą.
    if ttl > 0 do
      members |> Enum.each(fn pid -> GenServer.cast(pid, {:put_player, number, name, ttl - 1}) end)
    end

    case number do
      :player1 ->
        {:noreply, %State{state | player1: name}}
      :player2 ->
        {:noreply, %State{state | player2: name}}
    end
  end

  @impl GenServer
  def handle_cast({:make_move, number, move, ttl}, state) do
    self = self()
    # syn.members Returns the list of all members for GroupName in the specified Scope.
    # Kiekvieną procesų grupėje esantį pid'ą išskyrus save įsikelti į members kintamąjį.
    members = for {pid, _} <- :syn.members(:dist_sys_naive, :node), pid != self, do: pid

    ## Kiekvienam kitam memberiui perduoti atsakymą.
    if ttl > 0 do
      members |> Enum.each(fn pid -> GenServer.cast(pid, {:make_move, number, move, ttl - 1}) end)
    end

    case number do
      :player1 ->
        if rem(state.scalarClock, 2) == 0 do
          {:noreply, state}
        else
          {:noreply, %State{state | board: List.replace_at(state.board, move, "X"), scalarClock: state.scalarClock + 1}}
        end
      :player2 ->
        if rem(state.scalarClock, 2) == 1 do
          {:noreply, state}
        else
          {:noreply, %State{state | board: List.replace_at(state.board, move, "O"), scalarClock: state.scalarClock + 1}}
      end
    end
  end

end
