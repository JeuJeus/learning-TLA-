------------------------ MODULE SemaphoresTrivialTest ------------------------
EXTENDS SemaphoresTrivial

CalculationFinished == \A p \in numberOfProcesses: pc[p] = "Done"
ResultMatches == CalculationFinished => x = N

SemaphoresWork == \A i,j \in numberOfProcesses:
    (pc[i] \in {"read","write"}) /\ (pc[j] \in {"read","write"}) => (i=j)

=============================================================================
\* Modification History
\* Last modified Tue Mar 12 13:22:24 CET 2024 by jeujeus
\* Created Tue Mar 12 12:58:14 CET 2024 by jeujeus
