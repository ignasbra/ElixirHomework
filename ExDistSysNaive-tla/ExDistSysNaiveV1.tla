---------------------------- MODULE ExDistSysNaiveV1 ---------------------------
(*
We will add ranks here to achieve eventual consistency.
*)
EXTENDS Naturals, FiniteSets
CONSTANT Nodes
CONSTANT Values
CONSTANT Ranks
VARIABLE proc \* State of processes.
VARIABLE msgs \* All messages that were sent.
ASSUME Cardinality(Ranks) >= Cardinality(Values)
vars == <<msgs, proc>>
Msgs == UNION {
    [t: {"C_SEND"}, v: Values, dst: Nodes],
    [t: {"B_CAST"}, v: Values, src: Nodes, dst: Nodes]
}
MsgBCast(v, src, dst) == [t |-> "B_CAST", v |-> v, src |-> src, dst |-> dst]

Rank == CHOOSE r \in [Values -> Ranks] :
    \A v1, v2 \in Values:
        v1 # v2 => r[v1] < r[v2] \/ r[v1] > r[v2]

Better(v1, v2) ==
    CASE v1 = v2             -> v1
      [] Rank[v1] > Rank[v2] -> v1
      [] Rank[v1] < Rank[v2] -> v2

TypeOK ==
    /\ proc \in [Nodes -> Values]
    /\ msgs \subseteq Msgs
--------------------------------------------------------------------------------
RecvCSend ==
    \E m \in msgs :
        /\ m.t = "C_SEND"
        /\ proc' = [proc EXCEPT ![m.dst] = Better(m.v, @)]
        /\ msgs' = (msgs \ {m}) \cup {MsgBCast(m.v, m.dst, n) : n \in Nodes}

RecvBCast ==
    \E m \in msgs :
        /\ m.t = "B_CAST"
        /\ proc' = [proc EXCEPT ![m.dst] = Better(m.v, @)]
        /\ msgs' = msgs \ {m}

--------------------------------------------------------------------------------
Init ==
    LET v == CHOOSE v \in Values : TRUE
    IN  /\ proc = [n \in Nodes |-> v]
        /\ msgs \in SUBSET [t: {"C_SEND"}, v: Values, dst: Nodes]
Next ==
    \/ RecvCSend
    \/ RecvBCast
Fairness == WF_vars(Next)
Spec == Init /\ [][Next]_vars /\ Fairness
--------------------------------------------------------------------------------
EventuallyConsistent ==
    <>[] \E v \in Values : \A n \in Nodes : proc[n] = v

THEOREM Spec => []TypeOK /\ EventuallyConsistent
================================================================================
