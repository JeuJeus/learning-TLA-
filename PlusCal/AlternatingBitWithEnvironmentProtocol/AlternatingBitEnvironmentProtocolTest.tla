------------------------ MODULE AlternatingBitEnvironmentProtocolTest ------------------------
EXTENDS AlternatingBitEnvironmentProtocol

LimitLengthOfQueuesToThree == (Len(aToB) <= 3) /\ (Len(bToA) <= 3) /\ (Len(eVar) <= 3)

ABESpec_TypeOK == ABE_Spec!ABESpec_TypeOK

ABESpec_TransmissionWorking == ABE_Spec!ABESpec_TransmissionWorking
=============================================================================