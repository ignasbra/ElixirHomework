---------------------------- MODULE ExDistSysNaiveV0 ---------------------------
CONSTANT Nodes
CONSTANT Values
VARIABLE proc \* State of processes.
VARIABLE msgs \* All messages that were sent.
vars == <<msgs, proc>>
Msgs == UNION {
    [t: {"C_SEND"}, v: Values, dst: Nodes],
    [t: {"B_CAST"}, v: Values, src: Nodes, dst: Nodes]
}
MsgBCast(v, src, dst) == [t |-> "B_CAST", v |-> v, src |-> src, dst |-> dst]

TypeOK ==
    /\ proc \in [Nodes -> Values]
    /\ msgs \subseteq Msgs
--------------------------------------------------------------------------------
RecvCSend ==
    \E m \in msgs :
        /\ m.t = "C_SEND"
        /\ proc' = [proc EXCEPT ![m.dst] = m.v]
        /\ msgs' = (msgs \ {m}) \cup {MsgBCast(m.v, m.dst, n) : n \in Nodes}

RecvBCast ==
    \E m \in msgs :
        /\ m.t = "B_CAST"
        /\ proc' = [proc EXCEPT ![m.dst] = m.v]
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
