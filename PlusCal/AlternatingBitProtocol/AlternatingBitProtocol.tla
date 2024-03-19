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
    
    fair process(ASend = "ASend") {
        aSend:  
            while(TRUE) {
                aSendMsgToB() 
            } 
    }
    
    fair+ process(AReceive = "AReceive") {
        aReceive:  
            while(TRUE) {
                await bToA /= << >>;
                if(Head(bToA) = aVar.bit) {
                    with (d \in Data) {
                        aSetNewMessageToBeSent()
                    }
                };
                markMessageAsRecievedFromBToA()
            }      
    }

    fair process(BSend = "BSend") {
        bSend:  
            while(TRUE) {
                bSentAckToA() 
            } 
    }
    
    fair+ process(BReceive = "BReceive") {
        bReceive:  
            while(TRUE) {
                await aToB /= << >>;
                if(Head(aToB).bit /= bVar.bit) {
                    setExpectedMessage()
                };
                markMessageAsRecievedFromAToB()
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
\* BEGIN TRANSLATION (chksum(pcal) = "4e87c7cb" /\ chksum(tla) = "f004f6b1")
VARIABLES aVar, bVar, aToB, bToA

vars == << aVar, bVar, aToB, bToA >>

ProcSet == {"ASend"} \cup {"AReceive"} \cup {"BSend"} \cup {"BReceive"} \cup {"L"}

Init == (* Global variables *)
        /\ aVar \in Messages
        /\ bVar = aVar
        /\ aToB = << >>
        /\ bToA = << >>

ASend == /\ aToB' = Append(aToB, aVar)
         /\ UNCHANGED << aVar, bVar, bToA >>

AReceive == /\ bToA /= << >>
            /\ IF Head(bToA) = aVar.bit
                  THEN /\ \E d \in Data:
                            aVar' = [data |-> d, bit |-> 1 - aVar.bit]
                  ELSE /\ TRUE
                       /\ aVar' = aVar
            /\ bToA' = Tail(bToA)
            /\ UNCHANGED << bVar, aToB >>

BSend == /\ bToA' = Append(bToA, bVar.bit)
         /\ UNCHANGED << aVar, bVar, aToB >>

BReceive == /\ aToB /= << >>
            /\ IF Head(aToB).bit /= bVar.bit
                  THEN /\ bVar' = Head(aToB)
                  ELSE /\ TRUE
                       /\ bVar' = bVar
            /\ aToB' = Tail(aToB)
            /\ UNCHANGED << aVar, bToA >>

LoseMessages == /\ \/ /\ \E i \in 1..Len(aToB):
                           aToB' = RemoveElement(i, aToB)
                      /\ bToA' = bToA
                   \/ /\ \E i \in 1..Len(bToA):
                           bToA' = RemoveElement(i, bToA)
                      /\ aToB' = aToB
                /\ UNCHANGED << aVar, bVar >>

Next == ASend \/ AReceive \/ BSend \/ BReceive \/ LoseMessages

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(ASend)
        /\ SF_vars(AReceive)
        /\ WF_vars(BSend)
        /\ SF_vars(BReceive)

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
\* Last modified Tue Mar 19 15:47:44 CET 2024 by jeujeus
\* Created Fri Mar 15 12:00:55 CET 2024 by jeujeus
