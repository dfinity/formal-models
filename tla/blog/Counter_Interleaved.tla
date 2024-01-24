---- MODULE Counter_Interleaved ----

EXTENDS Naturals

INCREASE_PIDS == {1, 2}

(* --algorithm Counter {

variables
    cnt \in {0, 1};
    cumulative_increment = 0;

process (Increase \in INCREASE_PIDS)
    variable
        increment;
{
Loop:
    with(i \in 1..2) {
        increment := i;
        cumulative_increment := cumulative_increment + increment;
    };
Suspend:
    cnt := cnt + cumulative_increment;
    cumulative_increment := 0;
    goto Loop;
}

} *)
\* BEGIN TRANSLATION (chksum(pcal) = "e42d2960" /\ chksum(tla) = "f859d006")
CONSTANT defaultInitValue
VARIABLES cnt, cumulative_increment, pc, increment

vars == << cnt, cumulative_increment, pc, increment >>

ProcSet == (INCREASE_PIDS)

Init == (* Global variables *)
        /\ cnt \in {0, 1}
        /\ cumulative_increment = 0
        (* Process Increase *)
        /\ increment = [self \in INCREASE_PIDS |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> "Loop"]

Loop(self) == /\ pc[self] = "Loop"
              /\ \E i \in 1..2:
                   /\ increment' = [increment EXCEPT ![self] = i]
                   /\ cumulative_increment' = cumulative_increment + increment'[self]
              /\ pc' = [pc EXCEPT ![self] = "Suspend"]
              /\ cnt' = cnt

Suspend(self) == /\ pc[self] = "Suspend"
                 /\ cnt' = cnt + cumulative_increment
                 /\ cumulative_increment' = 0
                 /\ pc' = [pc EXCEPT ![self] = "Loop"]
                 /\ UNCHANGED increment

Increase(self) == Loop(self) \/ Suspend(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in INCREASE_PIDS: Increase(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

====
