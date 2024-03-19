------------------------ MODULE AlternatingBitProtocolTest ------------------------
EXTENDS AlternatingBitProtocol

LimitLengthOfQueuesToThree == (Len(aToB) <= 3) /\ (Len(bToA) <= 3)

ABSpec_TypeOK == AB_Spec!ABSpec_TypeOK

ABSpec_VariablesChanging == AB_Spec!VariablesChanging
=============================================================================