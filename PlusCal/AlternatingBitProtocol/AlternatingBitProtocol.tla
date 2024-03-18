----------------------- MODULE AlternatingBitProtocol -----------------------
EXTENDS Integers, Sequences, TLC

CONSTANT Data
 
RemoveElement(i, sequence) == 
    [j \in 1..(Len(sequence)-1) |-> 
        IF j < i THEN sequence[j] 
            ELSE sequence[j+1]]
                                
Messages == [data : Data, bit : {0,1}]

(*--algorithm ab{
    variables 
        aVar \in Messages,
        bVar = aVar,
        aToB = << >>,
        bToA = << >>;
        
    macro aSendMsgToB(){
        aToB := Append(aToB, aVar)
    }
    
    macro aSetNewMessageToBeSent() {
        aVar := [data |-> d, bit |-> 1 - aVar.bit]
    }
    
    macro markMessageAsRecievedFromBToA(){
        bToA := Tail(bToA)
    }
    
    macro bSentAckToA() {
        bToA := Append(bToA, bVar.bit)
    }
    
    macro setExpectedMessage() {
        bVar := Head(aToB)
    }
    
    macro markMessageAsRecievedFromAToB() {
        aToB := Tail(aToB)
    }
    
    macro looseSomeMsgFromAToB(i){
        aToB := RemoveElement(i, aToB)
    }
    
    macro looseSomeMsgFromBToA(i){
        bToA := RemoveElement(i, bToA)
    }
    
    process(A = "A") {
        a:  while(TRUE) {
                either { 
                    aSendMsgToB() 
                } or {
                    await bToA /= << >>;
                    if(Head(bToA) = aVar.bit) {
                        with (d \in Data) {
                            aSetNewMessageToBeSent()
                        }
                    };
                    markMessageAsRecievedFromBToA()
                }      
            }
    }

    process(B = "B") {
        b:  while(TRUE){
                either {
                    bSentAckToA()
                } or {
                    await aToB /= << >>;
                    if(Head(aToB).bit /= bVar.bit) {
                        setExpectedMessage()
                    };
                    markMessageAsRecievedFromAToB()
                }
            }
    }
    
    process(LoseMessages = "L") {
        l:  while(TRUE){
            either with(i \in 1..Len(aToB)) {
                looseSomeMsgFromAToB(i)
            } or with(i \in 1..Len(bToA)) {
                looseSomeMsgFromBToA(i)
            }
        }
    }

}*)
\* BEGIN TRANSLATION (chksum(pcal) = "246eeb0e" /\ chksum(tla) = "a28b4a06")
VARIABLES aVar, bVar, aToB, bToA

vars == << aVar, bVar, aToB, bToA >>

ProcSet == {"A"} \cup {"B"} \cup {"L"}

Init == (* Global variables *)
        /\ aVar \in Messages
        /\ bVar = aVar
        /\ aToB = << >>
        /\ bToA = << >>

A == /\ \/ /\ aToB' = Append(aToB, aVar)
           /\ UNCHANGED <<aVar, bToA>>
        \/ /\ bToA /= << >>
           /\ IF Head(bToA) = aVar.bit
                 THEN /\ \E d \in Data:
                           aVar' = [data |-> d, bit |-> 1 - aVar.bit]
                 ELSE /\ TRUE
                      /\ aVar' = aVar
           /\ bToA' = Tail(bToA)
           /\ aToB' = aToB
     /\ bVar' = bVar

B == /\ \/ /\ bToA' = Append(bToA, bVar.bit)
           /\ UNCHANGED <<bVar, aToB>>
        \/ /\ aToB /= << >>
           /\ IF Head(aToB).bit /= bVar.bit
                 THEN /\ bVar' = Head(aToB)
                 ELSE /\ TRUE
                      /\ bVar' = bVar
           /\ aToB' = Tail(aToB)
           /\ bToA' = bToA
     /\ aVar' = aVar

LoseMessages == /\ \/ /\ \E i \in 1..Len(aToB):
                           aToB' = RemoveElement(i, aToB)
                      /\ bToA' = bToA
                   \/ /\ \E i \in 1..Len(bToA):
                           bToA' = RemoveElement(i, bToA)
                      /\ aToB' = aToB
                /\ UNCHANGED << aVar, bVar >>

Next == A \/ B \/ LoseMessages

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

AB_TypeOK == 
    /\ aVar \in Messages
    /\ bVar \in Messages
    /\ aToB \in Seq(Messages)
    /\ bToA \in Seq({0,1})

EqualityInvariant == (bToA # << >>) /\ (Head(bToA) = aVar.bit) => (aVar = bVar)

IsConcatenationOfTwoSingleValues(sequence,x,y) == 
    \E i \in 0..Len(sequence) :
        \A j \in 1..Len(sequence) : sequence[j] = IF j <= i THEN x ELSE y

IsConcatenationOfTwoSingleValuesFromType(sequence, allowedType) == 
    \E x,y \in allowedType : IsConcatenationOfTwoSingleValues(sequence,x,y)             

ConcatenationInvariant == 
        /\ IsConcatenationOfTwoSingleValuesFromType(aToB, Messages) 
        /\ IsConcatenationOfTwoSingleValuesFromType(bToA, {0,1})   

AB_Spec == INSTANCE AlternatingBitSpec
        
=============================================================================
\* Modification History
\* Last modified Mon Mar 18 14:47:01 CET 2024 by jeujeus
\* Created Fri Mar 15 12:00:55 CET 2024 by jeujeus
