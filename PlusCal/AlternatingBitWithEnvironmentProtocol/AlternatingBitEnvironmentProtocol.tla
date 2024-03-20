----------------------- MODULE AlternatingBitEnvironmentProtocol -----------------------
EXTENDS Integers, Sequences, TLC

CONSTANT Data
 
RemoveElement(i, sequence) == 
    [j \in 1..(Len(sequence)-1) |-> 
        IF j < i THEN sequence[j] 
            ELSE sequence[j+1]]
                                
Messages == [data : Data, bit : {0,1}]

(*--algorithm abe{
    variables 
        aVar \in Messages,
        bVar = aVar,
        eVar \in Data,
        eQueue = << >>,
        aToB = << >>,
        bToA = << >>;
        
    macro aSendMsgToB(){
        aToB := Append(aToB, aVar)
    }
    
    macro aSetNewMessageToBeSent() {
        aVar := [data |-> Head(eQueue), bit |-> 1 - aVar.bit];
        eQueue := Tail(eQueue);
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
    
    macro eChooseMsg(data) {
        eVar := data;
        eQueue := Append(eQueue,eVar)
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
                    await eQueue /= <<>>;
                    aSetNewMessageToBeSent()                    
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

    fair+ process(chooseMessage = "E") {
        e: while(TRUE){
            with (d \in Data) {
                eChooseMsg(d)
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
\* BEGIN TRANSLATION (chksum(pcal) = "7492a03d" /\ chksum(tla) = "bb4df935")
VARIABLES aVar, bVar, eVar, eQueue, aToB, bToA

vars == << aVar, bVar, eVar, eQueue, aToB, bToA >>

ProcSet == {"ASend"} \cup {"AReceive"} \cup {"BSend"} \cup {"BReceive"} \cup {"E"} \cup {"L"}

Init == (* Global variables *)
        /\ aVar \in Messages
        /\ bVar = aVar
        /\ eVar \in Data
        /\ eQueue = << >>
        /\ aToB = << >>
        /\ bToA = << >>

ASend == /\ aToB' = Append(aToB, aVar)
         /\ UNCHANGED << aVar, bVar, eVar, eQueue, bToA >>

AReceive == /\ bToA /= << >>
            /\ IF Head(bToA) = aVar.bit
                  THEN /\ eQueue /= <<>>
                       /\ aVar' = [data |-> Head(eQueue), bit |-> 1 - aVar.bit]
                       /\ eQueue' = Tail(eQueue)
                  ELSE /\ TRUE
                       /\ UNCHANGED << aVar, eQueue >>
            /\ bToA' = Tail(bToA)
            /\ UNCHANGED << bVar, eVar, aToB >>

BSend == /\ bToA' = Append(bToA, bVar.bit)
         /\ UNCHANGED << aVar, bVar, eVar, eQueue, aToB >>

BReceive == /\ aToB /= << >>
            /\ IF Head(aToB).bit /= bVar.bit
                  THEN /\ bVar' = Head(aToB)
                  ELSE /\ TRUE
                       /\ bVar' = bVar
            /\ aToB' = Tail(aToB)
            /\ UNCHANGED << aVar, eVar, eQueue, bToA >>

chooseMessage == /\ \E d \in Data:
                      /\ eVar' = d
                      /\ eQueue' = Append(eQueue,eVar')
                 /\ UNCHANGED << aVar, bVar, aToB, bToA >>

LoseMessages == /\ \/ /\ \E i \in 1..Len(aToB):
                           aToB' = RemoveElement(i, aToB)
                      /\ bToA' = bToA
                   \/ /\ \E i \in 1..Len(bToA):
                           bToA' = RemoveElement(i, bToA)
                      /\ aToB' = aToB
                /\ UNCHANGED << aVar, bVar, eVar, eQueue >>

Next == ASend \/ AReceive \/ BSend \/ BReceive \/ chooseMessage
           \/ LoseMessages

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(ASend)
        /\ SF_vars(AReceive)
        /\ WF_vars(BSend)
        /\ SF_vars(BReceive)
        /\ SF_vars(chooseMessage)

\* END TRANSLATION 

ABE_TypeOK == 
    /\ aVar \in Messages
    /\ bVar \in Messages
    /\ eVar \in Data
    /\ eQueue \in Seq(Data)
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

ABE_Spec == INSTANCE AlternatingBitEnvironmentSpec
        
=============================================================================
\* Modification History
\* Last modified Wed Mar 20 09:23:52 CET 2024 by jeujeus
\* Created Fri Mar 15 12:00:55 CET 2024 by jeujeus
