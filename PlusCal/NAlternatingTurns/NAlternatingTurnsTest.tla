------------------------- MODULE NAlternatingTurnsTest -------------------------
EXTENDS NAlternatingTurns

ProcessIsInCsImpliesItsHisTurn == \A i \in processes : (pc[i] = "cs") => (turn = i)

MutualExclusion == \A j,k \in processes :
                        (j /= k) => ~((pc[j] = "cs") /\ (pc[k] = "cs"))

=============================================================================
\* Modification History
\* Last modified Tue Mar 12 15:20:18 CET 2024 by jeujeus
\* Created Tue Mar 12 15:11:32 CET 2024 by jeujeus
