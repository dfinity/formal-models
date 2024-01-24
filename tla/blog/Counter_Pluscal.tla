---- MODULE Counter_Pluscal ----

EXTENDS Naturals

INCREASE_PIDS == {1}

(* --algorithm Counter {

variable cnt \in {0, 1}

process (Increase \in INCREASE_PIDS)
    variable
        increment;
{
Loop:
    with(i \in 1..2) {
        increment := i;
    };
    cnt := cnt + increment;
    goto Loop;
}

} *)
\* BEGIN TRANSLATION (chksum(pcal) = "caaf0364" /\ chksum(tla) = "2c195c83")
CONSTANT defaultInitValue
VARIABLES cnt, pc, increment

vars == << cnt, pc, increment >>

ProcSet == (INCREASE_PIDS)

Init == (* Global variables *)
        /\ cnt \in {0, 1}
        (* Process Increase *)
        /\ increment = [self \in INCREASE_PIDS |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> "Loop"]

Loop(self) == /\ pc[self] = "Loop"
              /\ \E i \in 1..2:
                   increment' = [increment EXCEPT ![self] = i]
              /\ cnt' = cnt + increment'[self]
              /\ pc' = [pc EXCEPT ![self] = "Loop"]

Increase(self) == Loop(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in INCREASE_PIDS: Increase(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

====
