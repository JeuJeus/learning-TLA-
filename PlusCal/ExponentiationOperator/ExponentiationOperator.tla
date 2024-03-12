----------------------- MODULE ExponentiationOperator -----------------------

EXTENDS Integers, Sequences, TLC

CONSTANT valuesForM, valuesForN
ASSUME  /\ valuesForM \subseteq Int
        /\ valuesForN \subseteq Int
        /\ \A n \in valuesForN : n >= 0
        
(* --algorithm exponential {
    
    variables 
        m \in valuesForM,
        n \in valuesForN,
        result = 1,
        i = 1;
        
    {
        while(i<=n){
            result := m*result;
            i := i+1;
        };
        
        assert result = m^n;
    }

} *)
\* BEGIN TRANSLATION (chksum(pcal) = "d01051e0" /\ chksum(tla) = "2d8cab5c")
VARIABLES m, n, result, i, pc

vars == << m, n, result, i, pc >>

Init == (* Global variables *)
        /\ m \in valuesForM
        /\ n \in valuesForN
        /\ result = 1
        /\ i = 1
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF i<=n
               THEN /\ result' = m*result
                    /\ i' = i+1
                    /\ pc' = "Lbl_1"
               ELSE /\ Assert(result = m^n, 
                              "Failure of assertion at line 24, column 9.")
                    /\ pc' = "Done"
                    /\ UNCHANGED << result, i >>
         /\ UNCHANGED << m, n >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Tue Mar 12 09:07:13 CET 2024 by jeujeus
\* Created Tue Mar 12 09:02:27 CET 2024 by jeujeus
