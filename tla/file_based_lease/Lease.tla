---- MODULE Lease ----
EXTENDS TLC, Sequences, SequencesExt, Integers, FiniteSets, FiniteSetsExt

CONSTANT 
    PROCESSES,
    MARK_EXPIRED_ID

Symmetry_Sets == {PROCESSES}
Symmetry_Permutations == UNION { Permutations(S) : S \in Symmetry_Sets }

Remove_File(fs, id) ==
    { f \in fs: f.id # id }

Is_Expired(fs, idx) ==
    \/ \E f \in fs: f.id = idx /\ f.expired
    \* Treating missing files as expired doesn't work
    \* \/ \A f \in fs: f.id # idx

Already_Exists(files, n) ==
    \E f \in files: f.id = n

Move(fs, from, to) ==
    LET 
        from_f == CHOOSE f \in fs: f.id = from
        to_f_set == IF \E f \in fs: f.id = to 
            THEN {f \in fs: f.id = to}
            ELSE {}
    IN (fs \ ({from_f} \cup to_f_set)) \cup {[ from_f EXCEPT !.id = to ]}

(* --algorithm lease {

variables
    files = {};
    result_buffer = [ p \in PROCESSES |-> FALSE ];
    critical = {};
    dead = {};

macro atomic_create(n) {
    if(Already_Exists(files, n)) {
        result_buffer[self] := FALSE;
    } else {
        files := files \cup {[ id |-> n, pid |-> self, expired |-> FALSE ]};
        result_buffer[self] := TRUE;
    }
}

process (Client \in PROCESSES) 
    variable
        idx = 0;
{
    Lease_Begin:
        atomic_create(0);
    Wait_For_Lock_0:
        if(result_buffer[self]) {
            goto Critical;
        };
    Check_Stale:
        idx := 0;
        result_buffer[self] := Is_Expired(files, idx);
    Wait_For_Stale:
        if(~result_buffer[self]) {
            goto Lease_Begin;
        } else {
            atomic_create(idx + 1);
        };
    Wait_For_Lock_1:
        if(~result_buffer[self]) {
            idx := idx + 1;
            goto Check_Stale;
        } else {
            result_buffer[self] := Is_Expired(files, idx);
        };
    Wait_For_Stale_1:
        if(~result_buffer[self]) {
            files := Remove_File(files, idx + 1);
            goto Lease_Begin;
        } else {
            files := Move(files, idx + 1, idx);
        };
    Rename_Loop:
        if(idx > 0) {
            idx := idx - 1;
            files := Move(files, idx + 1, idx);
            goto Rename_Loop;
        } else {
            files := Remove_File(files, 0);
            goto Lease_Begin;
        };
    Critical:
        critical := critical \cup {self};
   Release:
        critical := critical \ {self};
        files := { f \in files: f.id # 0 };
        goto Lease_Begin;
}

process (Mark_Expired = MARK_EXPIRED_ID) {
    Loop_Expiry:
    while(TRUE) {
        with(f \in { f2 \in files: f2.pid \in dead /\ ~f2.expired} ) {
            files := (files \ {f}) \cup {[ f EXCEPT !.expired = TRUE ]};
        }
    }
}

}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "86d78cf1" /\ chksum(tla) = "88c6281e")
VARIABLES pc, files, result_buffer, critical, dead, idx

vars == << pc, files, result_buffer, critical, dead, idx >>

ProcSet == (PROCESSES) \cup {MARK_EXPIRED_ID}

Init == (* Global variables *)
        /\ files = {}
        /\ result_buffer = [ p \in PROCESSES |-> FALSE ]
        /\ critical = {}
        /\ dead = {}
        (* Process Client *)
        /\ idx = [self \in PROCESSES |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self \in PROCESSES -> "Lease_Begin"
                                        [] self = MARK_EXPIRED_ID -> "Loop_Expiry"]

Lease_Begin(self) == /\ pc[self] = "Lease_Begin"
                     /\ IF Already_Exists(files, 0)
                           THEN /\ result_buffer' = [result_buffer EXCEPT ![self] = FALSE]
                                /\ files' = files
                           ELSE /\ files' = (files \cup {[ id |-> 0, pid |-> self, expired |-> FALSE ]})
                                /\ result_buffer' = [result_buffer EXCEPT ![self] = TRUE]
                     /\ pc' = [pc EXCEPT ![self] = "Wait_For_Lock_0"]
                     /\ UNCHANGED << critical, dead, idx >>

Wait_For_Lock_0(self) == /\ pc[self] = "Wait_For_Lock_0"
                         /\ IF result_buffer[self]
                               THEN /\ pc' = [pc EXCEPT ![self] = "Critical"]
                               ELSE /\ pc' = [pc EXCEPT ![self] = "Check_Stale"]
                         /\ UNCHANGED << files, result_buffer, critical, dead, 
                                         idx >>

Check_Stale(self) == /\ pc[self] = "Check_Stale"
                     /\ idx' = [idx EXCEPT ![self] = 0]
                     /\ result_buffer' = [result_buffer EXCEPT ![self] = Is_Expired(files, idx'[self])]
                     /\ pc' = [pc EXCEPT ![self] = "Wait_For_Stale"]
                     /\ UNCHANGED << files, critical, dead >>

Wait_For_Stale(self) == /\ pc[self] = "Wait_For_Stale"
                        /\ IF ~result_buffer[self]
                              THEN /\ pc' = [pc EXCEPT ![self] = "Lease_Begin"]
                                   /\ UNCHANGED << files, result_buffer >>
                              ELSE /\ IF Already_Exists(files, (idx[self] + 1))
                                         THEN /\ result_buffer' = [result_buffer EXCEPT ![self] = FALSE]
                                              /\ files' = files
                                         ELSE /\ files' = (files \cup {[ id |-> (idx[self] + 1), pid |-> self, expired |-> FALSE ]})
                                              /\ result_buffer' = [result_buffer EXCEPT ![self] = TRUE]
                                   /\ pc' = [pc EXCEPT ![self] = "Wait_For_Lock_1"]
                        /\ UNCHANGED << critical, dead, idx >>

Wait_For_Lock_1(self) == /\ pc[self] = "Wait_For_Lock_1"
                         /\ IF ~result_buffer[self]
                               THEN /\ idx' = [idx EXCEPT ![self] = idx[self] + 1]
                                    /\ pc' = [pc EXCEPT ![self] = "Check_Stale"]
                                    /\ UNCHANGED result_buffer
                               ELSE /\ result_buffer' = [result_buffer EXCEPT ![self] = Is_Expired(files, idx[self])]
                                    /\ pc' = [pc EXCEPT ![self] = "Wait_For_Stale_1"]
                                    /\ idx' = idx
                         /\ UNCHANGED << files, critical, dead >>

Wait_For_Stale_1(self) == /\ pc[self] = "Wait_For_Stale_1"
                          /\ IF ~result_buffer[self]
                                THEN /\ files' = Remove_File(files, idx[self] + 1)
                                     /\ pc' = [pc EXCEPT ![self] = "Lease_Begin"]
                                ELSE /\ files' = Move(files, idx[self] + 1, idx[self])
                                     /\ pc' = [pc EXCEPT ![self] = "Rename_Loop"]
                          /\ UNCHANGED << result_buffer, critical, dead, idx >>

Rename_Loop(self) == /\ pc[self] = "Rename_Loop"
                     /\ IF idx[self] > 0
                           THEN /\ idx' = [idx EXCEPT ![self] = idx[self] - 1]
                                /\ files' = Move(files, idx'[self] + 1, idx'[self])
                                /\ pc' = [pc EXCEPT ![self] = "Rename_Loop"]
                           ELSE /\ files' = Remove_File(files, 0)
                                /\ pc' = [pc EXCEPT ![self] = "Lease_Begin"]
                                /\ idx' = idx
                     /\ UNCHANGED << result_buffer, critical, dead >>

Critical(self) == /\ pc[self] = "Critical"
                  /\ critical' = (critical \cup {self})
                  /\ pc' = [pc EXCEPT ![self] = "Release"]
                  /\ UNCHANGED << files, result_buffer, dead, idx >>

Release(self) == /\ pc[self] = "Release"
                 /\ critical' = critical \ {self}
                 /\ files' = { f \in files: f.id # 0 }
                 /\ pc' = [pc EXCEPT ![self] = "Lease_Begin"]
                 /\ UNCHANGED << result_buffer, dead, idx >>

Client(self) == Lease_Begin(self) \/ Wait_For_Lock_0(self)
                   \/ Check_Stale(self) \/ Wait_For_Stale(self)
                   \/ Wait_For_Lock_1(self) \/ Wait_For_Stale_1(self)
                   \/ Rename_Loop(self) \/ Critical(self) \/ Release(self)

Loop_Expiry == /\ pc[MARK_EXPIRED_ID] = "Loop_Expiry"
               /\ \E f \in { f2 \in files: f2.pid \in dead /\ ~f2.expired}:
                    files' = ((files \ {f}) \cup {[ f EXCEPT !.expired = TRUE ]})
               /\ pc' = [pc EXCEPT ![MARK_EXPIRED_ID] = "Loop_Expiry"]
               /\ UNCHANGED << result_buffer, critical, dead, idx >>

Mark_Expired == Loop_Expiry

Next == Mark_Expired
           \/ (\E self \in PROCESSES: Client(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 


\* -------------------------
\* Modified transition relation
\* -------------------------

Next_With_Killing_And_Idling ==
    \/ Next
    \/ \E pid \in PROCESSES:
        /\ pc' = [pc EXCEPT ![pid] = "Done"]
        /\ dead' = dead \cup {pid}
        /\ UNCHANGED << files, result_buffer, critical, idx >>
    \/ 
        \* Allow idling if everyone is dead
        /\ dead = PROCESSES
        /\ UNCHANGED << files, result_buffer, critical, dead, idx, pc >>


\* -------------------------
\* Sanity checks
\* -------------------------

Cant_Reach_P_Processes ==
    Cardinality(files) < Cardinality(PROCESSES)

\* -------------------------
\* Properties
\* -------------------------

Only_One_Alive_Critical == Cardinality(critical \ dead ) <= 1

No_Two_Files_With_Same_Id ==
    \A f1, f2 \in files: f1.id = f2.id => f1 = f2

Fairness == 
    /\ WF_vars(Mark_Expired)
    /\ \A p \in PROCESSES:
        /\ WF_vars(Lease_Begin(p))
        /\ WF_vars(Wait_For_Lock_0(p))
        /\ WF_vars(Check_Stale(p))
        /\ WF_vars(Wait_For_Stale(p))
        /\ WF_vars(Wait_For_Lock_1(p))
        /\ WF_vars(Wait_For_Stale_1(p))
        /\ WF_vars(Rename_Loop(p))
        /\ WF_vars(Critical(p))
        /\ WF_vars(Release(p))

Spec_With_Fairness ==
    /\ Init
    /\ [][Next_With_Killing_And_Idling]_vars
    /\ Fairness

Everyone_Eventually_Gets_Lease_Or_Dies ==
    \A p \in PROCESSES: <>(p \in critical \cup dead)

====
