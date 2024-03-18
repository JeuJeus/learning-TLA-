------------------------ MODULE AlternatingBitProtocolTest ------------------------
EXTENDS AlternatingBitProtocol

LimitLengthOfQueuesToThree == (Len(aToB) <= 3) /\ (Len(bToA) <= 3)

=============================================================================