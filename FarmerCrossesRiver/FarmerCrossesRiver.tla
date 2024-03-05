------------------------- MODULE FarmerCrossesRiver -------------------------
EXTENDS Integers, FiniteSets

\*A farmer stands in front of a large river. It has no bridge. There is a fence on the other side.
\*He wants to bring over a wolf, a goat and a cabbage in his rowing boat. But he can only take one thing per trip!
\*ATTENTION: If the farmer is absent, the wolf can eat the goat and the goat can eat the cabbage.

VARIABLES carriage_on_side, boat, boat_side, last_carriage
vars == <<carriage_on_side, boat, boat_side, last_carriage>>

goods_to_transport == {"goat", "wulf", "cabbage"}
boat_docks == {"start", "end"}

-------------------------

Init ==  
    /\ carriage_on_side = [start |-> goods_to_transport, end |-> {}]
    /\ boat = {}
    /\ boat_side = "start"
    /\ last_carriage = "NULL"

-------------------------

TypeOK == 
    /\ carriage_on_side \in [boat_docks -> SUBSET goods_to_transport]
    /\ boat \subseteq goods_to_transport
    /\ Cardinality(boat) <= 1
    /\ boat_side \in boat_docks
    /\ last_carriage \in {"NULL"} \cup goods_to_transport
    
-------------------------    

Safe(side) == 
    \/  /\ ({"goat", "wulf"} \subseteq side) = FALSE
        /\ ({"goat", "cabbage"} \subseteq side) = FALSE 
    \/  goods_to_transport \subseteq side
    
Consistent == 
    LET all_participants == (carriage_on_side["start"] \union carriage_on_side["end"] \union boat)
    IN  /\ all_participants \ goods_to_transport = {}
        /\ Cardinality(all_participants) = 3

------------------------- 

OtherSide(bs) == CHOOSE s \in boat_docks : s /= bs 

BoatIsEmpty == Cardinality(boat) = 0
BoatIsLoaded == Cardinality(boat) = 1
    
ThisSideCarriage == carriage_on_side[boat_side]

------------------------- 

UpdateCarriageStatus(new_this_side) ==
\* I would love to write something like this, but do not know how to use 
\* variable as string value for key in struct, TLC module toString does not help
\*    LET not_boat_side == OtherSide(boat_side)
\*    IN carriage_on_side' = [boat_side |-> new_this_side, not_boat_side |-> carriage_on_side["end"]]
    IF boat_side = "start"
        THEN carriage_on_side' = [start |-> new_this_side, end |-> carriage_on_side["end"]]                       
        ELSE carriage_on_side' = [end |-> new_this_side, start |-> carriage_on_side["start"]]
                      
UpdateBoatIfSafe(new_this_side, new_boat) ==
    /\ Safe(new_this_side)
    /\ boat' = new_boat
    /\ UNCHANGED boat_side
    /\ UpdateCarriageStatus(new_this_side)

------------------------- 

ChangeBoatContent(participant) ==
    /\  participant /= last_carriage
    /\  LET new_this_side == (ThisSideCarriage \ {participant}) \cup boat
            new_boat == {participant}
        IN  /\  last_carriage' = participant  
            /\ UpdateBoatIfSafe(new_this_side, new_boat)

UnloadBoat ==
    /\  BoatIsLoaded
    /\  LET new_this_side == ThisSideCarriage \cup boat
            new_boat == {}
        IN  /\ last_carriage' = last_carriage
            /\ UpdateBoatIfSafe(new_this_side, new_boat)

RowOverToOtherSide == 
    /\ boat_side' = OtherSide(boat_side) 
    /\ UNCHANGED <<carriage_on_side, boat, last_carriage>>
               
Transport == 
    \/  \E participant \in ThisSideCarriage : ChangeBoatContent(participant)
    \/  UnloadBoat
    \/  RowOverToOtherSide
            
-------------------------
    
Next == Consistent /\ Transport  

Spec == Init /\ [][Next]_vars

THEOREM Spec => []TypeOK

------------------------- 

\* Ensure we get a Stacktrace containing the Solution, set this as Invariant
NoSolution == Cardinality(carriage_on_side["end"]) < 3

=============================================================================
\* Modification History
\* Last modified Tue Mar 05 16:49:27 CET 2024 by jeujeus
\* Last modified Wed Feb 28 08:17:55 CET 2024 by JUFIGGE
\* Last modified Tue Feb 27 17:34:16 CET 2024 by JeuJeus
\* Created Mon Feb 26 12:41:56 CET 2024 by JeuJeus