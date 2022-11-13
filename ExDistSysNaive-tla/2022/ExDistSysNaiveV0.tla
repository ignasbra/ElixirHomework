---- MODULE ExDistSysNaiveV0 ----
EXTENDS TLC, TLAPS
CONSTANT Nodes  \* A set of node identifiers.
CONSTANT Values \* A set of possible values.
VARIABLE proc   \* State of the processes.
VARIABLE msgs   \* A set of messages sent.
vars == <<proc, msgs>>

Msgs == UNION {
    [t: {"C_SEND"}, dst: Nodes, v: Values],
    [t: {"B_CAST"}, src: Nodes, dst: Nodes, v: Values]
}
MsgBCast(src, dst, v) == [t |-> "B_CAST", src |-> src, dst |-> dst, v |-> v]

TypeOK ==
    /\ proc \in [Nodes -> Values]
    /\ msgs \subseteq Msgs
----------------------------------
RecvCSend ==
    \E m \in msgs :
        /\ m.t = "C_SEND"
        /\ proc' = [proc EXCEPT ![m.dst] = m.v]
        /\ msgs' = (msgs \ {m}) \cup {MsgBCast(m.dst, n,m.v): n \in (Nodes \ {m.dst})}
RecvBCast ==
    \E m \in msgs:
        /\ m.t = "B_CAST"
        /\ proc' = [proc EXCEPT ![m.dst] = m.v]
        /\ msgs' = msgs \ {m}
----------------------------------
Init ==
    \E v \in Values:
        /\ proc = [ n \in Nodes |-> v ]
        /\ msgs = [t: {"C_SEND"}, dst: Nodes, v: Values]

Next == RecvCSend \/ RecvBCast
Fairness == WF_vars(Next)
Spec == Init /\ [][Next]_vars /\ Fairness
----------------------------------
Consistent ==
    \E v \in Values :
            \A n \in Nodes :
               proc[n] = v
EventuallyConsistent ==
    <>[] Consistent
StrongConsistency == []Consistent

\* THEOREM Spec => /\ []TypeOK
                \* /\ []Consistent
                \* /\ EventuallyConsistent

THEOREM Spec => []TypeOK
  <1>1. Init => TypeOK BY DEF Init, TypeOK, Msgs
  <1>2. TypeOK /\ [Next]_vars => TypeOK'
    <2> SUFFICES ASSUME TypeOK, Next PROVE TypeOK' BY DEF vars, TypeOK
    <2>1. CASE RecvCSend BY <2>1 DEF RecvCSend, MsgBCast, TypeOK, Msgs
    <2>2. CASE RecvBCast BY <2>2 DEF RecvBCast, TypeOK, Msgs
    <2>q. QED BY <2>1, <2>2 DEF Next
  <1>q. QED BY <1>1, <1>2, PTL DEF Spec


==================================