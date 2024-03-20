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

------------------------- 

CorrectTower[disk \in 1..NumberOfDisks] == disk
InitialPuzzle[tower \in 1..3] == 
    IF tower = 1 
        THEN CorrectTower 
    ELSE <<>>

VARIABLE Towers    
TowerDomain == DOMAIN Towers
    
Init == Towers = InitialPuzzle

------------------------- 
    
TargetTowerIsEmpty(towerTo) == Len(towerTo) = 0

DiskIsSmallerOrTowerIsEmpty(towerFrom,towerTo) == 
    LET topElementOfOrigin == Head(towerFrom)
        topElementOfTarget == Head(towerTo)
    IN  IF TargetTowerIsEmpty(towerTo) 
            THEN TRUE 
        ELSE topElementOfTarget > topElementOfOrigin 

OriginTowerIsNotEmpty(towerFrom) == towerFrom /= <<>>

CanMoveDisk(towerFrom,towerTo) == 
    /\ OriginTowerIsNotEmpty(towerFrom)
    /\ DiskIsSmallerOrTowerIsEmpty(towerFrom,towerTo)

-------------------------    
    
MoveDisk(from,to,towerFrom,towerTo) ==
    LET fromWithoutTop == Tail(towerFrom)
        top == <<Head(towerFrom)>>
        topWithTopOnTop == top \o towerTo
    IN  Towers' = [Towers EXCEPT 
                    ![from] = fromWithoutTop,
                    ![to] = topWithTopOnTop]

Next == 
    \E from,to \in TowerDomain :
        LET towerFrom == Towers[from]
            towerTo == Towers[to]
        IN  /\ CanMoveDisk(towerFrom,towerTo)
            /\ MoveDisk(from,to,towerFrom,towerTo)

-------------------------

IsSorted(tower) ==
  \A i, j \in 1..Len(tower):
    i < j => tower[i] <= tower[j]

OnlyContainsAllowedNumberOfDisks == 
    Len(FlattenSeq(Towers)) = 5

TypeOK == 
    /\  \A tower \in TowerDomain :
            LET towerToCheck == Towers[tower]
            IN  /\ IsSorted(towerToCheck)
                /\ Len(towerToCheck) <= NumberOfDisks
    /\ OnlyContainsAllowedNumberOfDisks
    
-------------------------
        
Spec == 
    /\ Init 
    /\ [][Next]_Towers 

THEOREM Spec => []TypeOK

-------------------------

InvariantOrElseFinished == 
    Towers[3] /= CorrectTower

=============================================================================
\* Modification History
\* Last modified Wed Mar 20 17:16:09 CET 2024 by jeujeus
\* Created Wed Mar 20 13:27:31 CET 2024 by jeujeus