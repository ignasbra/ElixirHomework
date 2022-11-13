---- MODULE XandOs ----
EXTENDS TLC,Naturals, Sequences

VARIABLES board, scalarClock
symbols == {"X", "O", " "}
possibleSpaces == {1, 2, 3, 4, 5, 6, 7, 8, 9}

TypeOK ==  board \in [possibleSpaces ->  symbols]
Init == /\ board \in [possibleSpaces ->  { " " }]
        /\ scalarClock = 1

\* 1 | 2 | 3
\* 4 | 5 | 6
\* 7 | 8 | 9
                    \* horizontal lines
IsWinner(symbol) == \/ \A x \in 1..3 : board[x] = symbol
                    \/ \A x \in 4..6 : board[x] = symbol
                    \/ \A x \in 7..9 : board[x] = symbol
                    \* vertical lines
                    \/ \A x \in {1, 4, 7} : board[x] = symbol
                    \/ \A x \in {2, 5, 8} : board[x] = symbol
                    \/ \A x \in {3, 6, 9} : board[x] = symbol
                    \* diagonal lines
                    \/ \A x \in {1, 5, 9} : board[x] = symbol
                    \/ \A x \in {7, 5, 3} : board[x] = symbol

GetEmptySquares == {x \in 1..9 : board[x] = " "}
IsNoMoreMoves == GetEmptySquares = {}
IsAnyWinner == IsWinner("X") \/ IsWinner("O")
PlaceO == \E i \in GetEmptySquares : board' = [board EXCEPT ![i] = "O"]  
PlaceX == \E i \in GetEmptySquares : board' = [board EXCEPT ![i] = "X"]  

Next == /\ IF scalarClock % 2 = 1 THEN  PlaceO ELSE PlaceX
        /\ scalarClock' = scalarClock + 1
             
Spec == Init /\ [][Next]_board /\ WF_board(Next)

Termination == <> (IsAnyWinner \/ IsNoMoreMoves)

====