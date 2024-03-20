----------------------- MODULE AlternatingBitEnvironmentSpec -----------------------
EXTENDS Integers, Sequences, TLC

CONSTANT Data

Messages == [data: Data, bit : {0,1}]

(*--algorithm abeSpec {
    variables
        aVar \in Messages,
        bVar = aVar,
        eVar \in Data;
    
    process (A = "A") {
        a: while(TRUE) {
            await aVar.bit = bVar.bit;
            aVar := [data |-> eVar, bit |-> 1-aVar.bit]
        }
    }
    
    process (B = "B") {
        b: while(TRUE) {
            await aVar.bit /= bVar.bit;
            bVar := aVar;
        }
    }
    
    process (E = "E") {
        e: while(TRUE) {
            await aVar = bVar;
            with (d \in Data) {
                eVar := d;
            }
        }
    }
}*)
\* BEGIN TRANSLATION (chksum(pcal) = "35063c35" /\ chksum(tla) = "b8b37213")
VARIABLES aVar, bVar, eVar

vars == << aVar, bVar, eVar >>

ProcSet == {"A"} \cup {"B"} \cup {"E"}

Init == (* Global variables *)
        /\ aVar \in Messages
        /\ bVar = aVar
        /\ eVar \in Data

A == /\ aVar.bit = bVar.bit
     /\ aVar' = [data |-> eVar, bit |-> 1-aVar.bit]
     /\ UNCHANGED << bVar, eVar >>

B == /\ aVar.bit /= bVar.bit
     /\ bVar' = aVar
     /\ UNCHANGED << aVar, eVar >>

E == /\ aVar = bVar
     /\ \E d \in Data:
          eVar' = d
     /\ UNCHANGED << aVar, bVar >>

Next == A \/ B \/ E

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

ABESpec_TypeOK == 
    /\ aVar \in Messages
    /\ bVar \in Messages
    /\ eVar \in Data 
    
ABESpec_TransmissionWorking ==
    \/ (aVar.bit = bVar.bit) => (aVar = bVar)
    \/ (aVar.bit = bVar.bit /\ eVar = aVar.data) => (aVar = bVar /\ eVar = bVar.data)

=============================================================================
\* Modification History
\* Last modified Wed Mar 20 07:53:13 CET 2024 by jeujeus
\* Created Tue Mar 19 15:09:35 CET 2024 by jeujeus
