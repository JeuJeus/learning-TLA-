------------------------ MODULE SemaphoresTrivialTest ------------------------
EXTENDS SemaphoresTrivial

CalculationFinished == \A p \in numberOfProcesses: pc[p] = "Done"
ResultMatches == CalculationFinished => x = N

=============================================================================
\* Modification History
\* Last modified Tue Mar 12 13:22:24 CET 2024 by jeujeus
\* Created Tue Mar 12 12:58:14 CET 2024 by jeujeus
