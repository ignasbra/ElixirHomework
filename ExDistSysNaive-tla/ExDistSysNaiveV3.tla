---------------------------- MODULE ExDistSysNaiveV1 ---------------------------
(*
We will add ranks here to achieve eventual consistency.
*)
EXTENDS Naturals, FiniteSets, TLAPS
CONSTANT Nodes
CONSTANT Values
CONSTANT Ranks
VARIABLE proc \* State of processes.
VARIABLE msgs \* All messages that were sent.
VARIABLE rank
ASSUME Cardinality(Ranks) >= Cardinality(Values)
vars == <<msgs, proc, rank>>
Msgs == UNION {
    [t: {"C_SEND"}, v: Values, dst: Nodes],
    [t: {"B_CAST"}, v: Values, src: Nodes, dst: Nodes]
}
MsgBCast(v, src, dst) == [t |-> "B_CAST", v |-> v, src |-> src, dst |-> dst]


Better(v1, v2) ==
    IF v1 = v2 \/ rank[v1] > rank[v2] THEN v1 ELSE v2

TypeOK ==
    /\ proc \in [Nodes -> Values]
    /\ msgs \subseteq Msgs
--------------------------------------------------------------------------------
RecvCSend ==
    \E m \in msgs :
        /\ m.t = "C_SEND"
        /\ proc' = [proc EXCEPT ![m.dst] = Better(m.v, @)]
        /\ msgs' = (msgs \ {m}) \cup {MsgBCast(m.v, m.dst, n) : n \in Nodes}
        /\ UNCHANGED rank

RecvBCast ==
    \E m \in msgs :
        /\ m.t = "B_CAST"
        /\ proc' = [proc EXCEPT ![m.dst] = Better(m.v, @)]
        /\ msgs' = msgs \ {m}
        /\ UNCHANGED rank

--------------------------------------------------------------------------------
Init ==
    \E v \in Values :
        /\ proc = [n \in Nodes |-> v]
        /\ msgs \in SUBSET [t: {"C_SEND"}, v: Values, dst: Nodes]
        /\ rank \in [Values -> Ranks]
        /\ \A v1, v2 \in Values: v1 # v2 => rank[v1] < rank[v2] \/ rank[v1] > rank[v2]
Next ==
    \/ RecvCSend
    \/ RecvBCast
Fairness == WF_vars(Next)
Spec == Init /\ [][Next]_vars /\ Fairness
--------------------------------------------------------------------------------
EventuallyConsistent ==
    <>[] \E v \in Values : \A n \in Nodes : proc[n] = v

THEOREM Spec => []TypeOK /\ EventuallyConsistent

--------------------------------------------------------------------------------
LEMMA BetterType == \A v1, v2 \in Values : Better(v1, v2) \in Values
  BY DEF Better
LEMMA Spec => []TypeOK
  <1>1. Init => TypeOK BY DEF Init, TypeOK, Msgs
  <1>2. TypeOK /\ [Next]_vars => TypeOK'
    <2> SUFFICES ASSUME TypeOK, Next PROVE TypeOK' BY DEF vars, TypeOK
    <2>1. CASE RecvCSend BY <2>1, BetterType DEF RecvCSend, TypeOK, Msgs, MsgBCast
    <2>2. CASE RecvBCast BY <2>2, BetterType DEF RecvBCast, TypeOK, Msgs
    <2>3. QED BY <2>1, <2>2 DEF Next
  <1>3. QED BY <1>1, <1>2, PTL DEF Spec

================================================================================
