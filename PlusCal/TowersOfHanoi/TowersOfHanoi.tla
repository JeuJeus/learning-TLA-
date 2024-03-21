--------------------------- MODULE TowersOfHanoi ---------------------------
(***************************************************************************
    TOWERS OF HANOI is a classical Puzzle Game.
    It consists of three Rods on Top of which Disks with 
    various diameters can be stacked.
    In the beginning all disks are stacked with their order having decreasing
    diameter from bottom to top.
    The Puzzles idea is to move that stack, persisting the order to the far 
    right rod.
    
        =           |           |
       ===          |           |
      =====         |           |
     =======        |           |
        |           |           |
    
    Number of moves requied is 2^n -1, where n is the number of disks   
    
    Legal Moves:
    - Move one Disk at a time
    - \A Move : take upper disk from one stack, place it on top of another stack
    - Disks can not be placed on top of a smaller disk 
    
 ***************************************************************************)
EXTENDS Naturals, Sequences, TLC

------------------------- 

FlattenSeq(seqs) ==
  \* From TLA+ CommunityModules SequencesExt                                           
  IF Len(seqs) = 0 THEN seqs ELSE
    LET flatten[i \in 1..Len(seqs)] ==
        IF i = 1 THEN seqs[i] ELSE flatten[i-1] \o seqs[i]
    IN flatten[Len(seqs)] 

------------------------- 

CONSTANT NumberOfDisks
ASSUME NumberOfDisks \in Nat

CorrectTower[disk \in 1..NumberOfDisks] == disk
InitialPuzzle[tower \in 1..3] == 
    IF tower = 1 
        THEN CorrectTower 
    ELSE <<>>

(*--algorithm towersOfHanoi {
    \* built from TLA+ solution i already finished
    variables
        towers = InitialPuzzle,
        towersDomain = DOMAIN towers;
        
    define {
        TopElement(tower) == Head(tower)
        TowerWithoutTopElement(tower) == Tail(tower)
        TowerIsEmpty(tower) == tower = <<>>
        TowerIsNotEmpty(tower) == tower /= <<>>
        TowerWithNewTopElement(top,tower) == <<top>> \o tower
        WouldPlaceSmallerOnLargerDisk(fromTower,toTower) == TopElement(toTower) > TopElement(fromTower) 
        GameRulesFollowed(fromTower,toTower) == TowerIsEmpty(toTower) \/ WouldPlaceSmallerOnLargerDisk(fromTower,toTower)
    }
    
    procedure checkValidityAndMove(from=1,to=1)
        variables
            fromTower = towers[from],
            toTower = towers[to]; {
        if(TowerIsNotEmpty(fromTower) /\ GameRulesFollowed(fromTower,toTower)) {
            call move(from,to);
        };
        return;
    }
    
    procedure move(from=1,to=1)         
        variables
            fromTower = towers[from],
            toTower = towers[to]; {
        towers := [towers EXCEPT 
                    ![from] = TowerWithoutTopElement(fromTower),
                    ![to] = TowerWithNewTopElement(TopElement(fromTower),toTower)];
        return;
    }
            
    {
        while(TRUE) {
            with (origin \in towersDomain; target \in towersDomain) {
                call checkValidityAndMove(origin,target);
            }
        }
    }
}*)
\* BEGIN TRANSLATION (chksum(pcal) = "66abdfd5" /\ chksum(tla) = "16bf5e86")
\* Procedure variable fromTower of procedure checkValidityAndMove at line 54 col 13 changed to fromTower_
\* Procedure variable toTower of procedure checkValidityAndMove at line 55 col 13 changed to toTower_
\* Parameter from of procedure checkValidityAndMove at line 52 col 36 changed to from_
\* Parameter to of procedure checkValidityAndMove at line 52 col 43 changed to to_
VARIABLES towers, towersDomain, pc, stack

(* define statement *)
TopElement(tower) == Head(tower)
TowerWithoutTopElement(tower) == Tail(tower)
TowerIsEmpty(tower) == tower = <<>>
TowerIsNotEmpty(tower) == tower /= <<>>
TowerWithNewTopElement(top,tower) == <<top>> \o tower
WouldPlaceSmallerOnLargerDisk(fromTower,toTower) == TopElement(toTower) > TopElement(fromTower)
GameRulesFollowed(fromTower,toTower) == TowerIsEmpty(toTower) \/ WouldPlaceSmallerOnLargerDisk(fromTower,toTower)

VARIABLES from_, to_, fromTower_, toTower_, from, to, fromTower, toTower

vars == << towers, towersDomain, pc, stack, from_, to_, fromTower_, toTower_, 
           from, to, fromTower, toTower >>

Init == (* Global variables *)
        /\ towers = InitialPuzzle
        /\ towersDomain = DOMAIN towers
        (* Procedure checkValidityAndMove *)
        /\ from_ = 1
        /\ to_ = 1
        /\ fromTower_ = towers[from_]
        /\ toTower_ = towers[to_]
        (* Procedure move *)
        /\ from = 1
        /\ to = 1
        /\ fromTower = towers[from]
        /\ toTower = towers[to]
        /\ stack = << >>
        /\ pc = "Lbl_4"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF TowerIsNotEmpty(fromTower_) /\ GameRulesFollowed(fromTower_,toTower_)
               THEN /\ /\ from' = from_
                       /\ stack' = << [ procedure |->  "move",
                                        pc        |->  "Lbl_2",
                                        fromTower |->  fromTower,
                                        toTower   |->  toTower,
                                        from      |->  from,
                                        to        |->  to ] >>
                                    \o stack
                       /\ to' = to_
                    /\ fromTower' = towers[from']
                    /\ toTower' = towers[to']
                    /\ pc' = "Lbl_3"
               ELSE /\ pc' = "Lbl_2"
                    /\ UNCHANGED << stack, from, to, fromTower, toTower >>
         /\ UNCHANGED << towers, towersDomain, from_, to_, fromTower_, 
                         toTower_ >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ pc' = Head(stack).pc
         /\ fromTower_' = Head(stack).fromTower_
         /\ toTower_' = Head(stack).toTower_
         /\ from_' = Head(stack).from_
         /\ to_' = Head(stack).to_
         /\ stack' = Tail(stack)
         /\ UNCHANGED << towers, towersDomain, from, to, fromTower, toTower >>

checkValidityAndMove == Lbl_1 \/ Lbl_2

Lbl_3 == /\ pc = "Lbl_3"
         /\ towers' = [towers EXCEPT
                        ![from] = TowerWithoutTopElement(fromTower),
                        ![to] = TowerWithNewTopElement(TopElement(fromTower),toTower)]
         /\ pc' = Head(stack).pc
         /\ fromTower' = Head(stack).fromTower
         /\ toTower' = Head(stack).toTower
         /\ from' = Head(stack).from
         /\ to' = Head(stack).to
         /\ stack' = Tail(stack)
         /\ UNCHANGED << towersDomain, from_, to_, fromTower_, toTower_ >>

move == Lbl_3

Lbl_4 == /\ pc = "Lbl_4"
         /\ \E origin \in towersDomain:
              \E target \in towersDomain:
                /\ /\ from_' = origin
                   /\ stack' = << [ procedure |->  "checkValidityAndMove",
                                    pc        |->  "Lbl_4",
                                    fromTower_ |->  fromTower_,
                                    toTower_  |->  toTower_,
                                    from_     |->  from_,
                                    to_       |->  to_ ] >>
                                \o stack
                   /\ to_' = target
                /\ fromTower_' = towers[from_']
                /\ toTower_' = towers[to_']
                /\ pc' = "Lbl_1"
         /\ UNCHANGED << towers, towersDomain, from, to, fromTower, toTower >>

Next == checkValidityAndMove \/ move \/ Lbl_4

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 
IsSorted(tower) ==
  \A i, j \in 1..Len(tower):
    i < j => tower[i] <= tower[j]

OnlyContainsAllowedNumberOfDisks == 
    Len(FlattenSeq(towers)) = 5

TypeOK == 
    /\  \A tower \in towersDomain :
            LET towerToCheck == towers[tower]
            IN  /\ IsSorted(towerToCheck)
                /\ Len(towerToCheck) <= NumberOfDisks
    /\ OnlyContainsAllowedNumberOfDisks

THEOREM Spec => []TypeOK

InvariantOrElseFinished == 
    towers[3] /= CorrectTower

=============================================================================
\* Modification History
\* Last modified Thu Mar 21 09:13:36 CET 2024 by jeujeus
\* Created Wed Mar 20 09:29:51 CET 2024 by jeujeus
