--------------------- MODULE ExponentiationOperatorTest ---------------------
EXTENDS ExponentiationOperator

\* as per convention (https://stackoverflow.com/questions/59101827/how-can-i-set-constants-in-tla-configuration-file-when-using-vs-code)
\* configuration should be implemented this way
valuesForMRange == -8..-1 \cup 1..8
valuesForNRange == 0..10


=============================================================================
\* Modification History
\* Last modified Tue Mar 12 09:07:13 CET 2024 by jeujeus
\* Created Tue Mar 12 09:02:27 CET 2024 by jeujeus
