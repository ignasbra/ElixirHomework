---- MODULE XandOs ----
EXTENDS TLC
\* VARIABLES board, symbol

\* symbols == {"X", "O", " "}
\* TypeOK ==  (\A square \in board : square \in symbols)

\* --------------------------------------------------------------------------------
\* Init == /\ (board = { " ",  " ", " ", " ",  " ", " ", " ",  " ", " " }) 
\*         /\ symbol \in symbols

\* Next == /\ board' = {symbol} \cup board
\*         /\ board' = board \setminus symbol
\*         /\  \/ symbol' = "X"
\*             \/ symbol' = "O"
                 

\* Spec == Init /\ Next
--------------------------------------------------------------------------------


VARIABLES board
symbols == {"X", "O", " "}
legal == { "X", "O" }
possibleSpaces == {1, 2, 3, 4, 5, 6, 7, 8, 9}

TypeOK ==   /\ \A square \in board : square \in symbols

\* Init == board =  {1, 2, 3, 4, 5, 6, 7, 8, 9} \X { " " }
Init == board \in [{1, 2, 3, 4, 5, 6, 7, 8, 9} ->  { " " }]
\* PlaceO == \E i \in board : board' = [board EXCEPT ![i] = "X"]
\* PlaceX == \E i \in board : board' = [board EXCEPT ![i] = "O"]

\* PlaceX == \E i \in board : board' = (board \setminus {i}) \cup { <<i[1], "X">> } 
\* PlaceO == \E i \in board : board' = (board \setminus {i}) \cup { <<i[1], "O">> } 

GetEmptySquares == {x \in possibleSpaces : board[x] = " "}
\* IsNoMoreMoves == GetEmptySquares != { }

PlaceO == \E i \in GetEmptySquares : board' = [board EXCEPT ![i] = "O"]  
PlaceX == \E i \in GetEmptySquares : board' = [board EXCEPT ![i] = "X"]  

\* Next ==  IsMoreMoves /\ (PlaceO \/ PlaceX) 
Next ==  PlaceO \/ PlaceX 
            

Spec == Init /\ Next
====