------------------------------ MODULE TCommit ------------------------------
CONSTANT RM

VARIABLE rmState

TCTypeOK ==
  rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
 
TCConsistent ==
  \A r1, r2 \in RM : ~ /\ rmState[r1] = "aborted"
                       /\ rmState[r2] = "committed"
  
TCInit == rmState = [r \in RM |-> "working"]

canCommit == \A r \in RM : rmState[r] \in {"prepared", "committed"}

notCommitted == \A r \in RM : rmState[r] /= "committed"

Decide(r) == \/ /\ rmState[r] = "prepared"
                /\ canCommit
                /\ rmState' = [rmState EXCEPT ![r] = "committed"]
             \/ /\ rmState[r] \in {"working", "prepared"}
                /\ notCommitted
                /\ rmState' = [rmState EXCEPT ![r] = "aborted"]

Prepare(r) == /\ rmState[r] = "working"
              /\ rmState' = [rmState EXCEPT ![r] = "prepared"]

TCNext == \E r \in RM : Prepare(r) \/ Decide(r)

=============================================================================
\* Modification History
\* Last modified Sun Aug 05 12:33:58 IST 2018 by samurdha
\* Created Sun Aug 05 12:09:09 IST 2018 by samurdha
