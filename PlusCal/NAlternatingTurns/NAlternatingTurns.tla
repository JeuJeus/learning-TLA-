------------------------- MODULE NAlternatingTurns -------------------------
EXTENDS Integers, Sequences, TLC

CONSTANT N

(***************************************************************************
    NonCriticalSection<-|
        |               |
        v               |
      Enter             |
        |               | \A processes they in cyclic activity iterate over
        v               |   these states, which are not essentially atomic
    CriticalSection     |
        |               |
        v               |   
      Exit -------------|
 ***************************************************************************)

(* --algorithm NAlternatingTurns {
    variables 
        processes = 0..(N-1),
        turn \in processes;
        
        process(p \in processes){
            ncs: while(TRUE) {
                    skip;
            enter:  await turn = self;
            cs:     skip;
            exit:   turn := (turn+1)%N;
            }
        }
    
}*)
\* BEGIN TRANSLATION (chksum(pcal) = "7a3bcd04" /\ chksum(tla) = "3bd35e38")
VARIABLES processes, turn, pc

vars == << processes, turn, pc >>

ProcSet == (processes)

Init == (* Global variables *)
        /\ processes = 0..(N-1)
        /\ turn \in processes
        /\ pc = [self \in ProcSet |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "enter"]
             /\ UNCHANGED << processes, turn >>

enter(self) == /\ pc[self] = "enter"
               /\ turn = self
               /\ pc' = [pc EXCEPT ![self] = "cs"]
               /\ UNCHANGED << processes, turn >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "exit"]
            /\ UNCHANGED << processes, turn >>

exit(self) == /\ pc[self] = "exit"
              /\ turn' = (turn+1)%N
              /\ pc' = [pc EXCEPT ![self] = "ncs"]
              /\ UNCHANGED processes

p(self) == ncs(self) \/ enter(self) \/ cs(self) \/ exit(self)

Next == (\E self \in processes: p(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Tue Mar 12 15:32:06 CET 2024 by jeujeus
\* Created Tue Mar 12 15:11:32 CET 2024 by jeujeus
