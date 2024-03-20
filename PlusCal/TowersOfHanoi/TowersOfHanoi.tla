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
EXTENDS Naturals, Sequences

CONSTANT NumberOfDisks
ASSUME NumberOfDisks \in Nat

InitialFirstTowers == 
    [1..NumberOfDisks -> NumberOfDisks..1]
    
EmptyTower == << >>

(*--algorithm towersOfHanoi {
    variables
        initialTower \in InitialFirstTowers,
        pillars = [first |-> initialTower, second |-> EmptyTower, third |-> EmptyTower];
    
    {
        skip;
    }
}*)
\* BEGIN TRANSLATION (chksum(pcal) = "a82e5b1a" /\ chksum(tla) = "9723711d")
VARIABLES initialTower, pillars, pc

vars == << initialTower, pillars, pc >>

Init == (* Global variables *)
        /\ initialTower \in InitialFirstTowers
        /\ pillars = [first |-> initialTower, second |-> EmptyTower, third |-> EmptyTower]
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ TRUE
         /\ pc' = "Done"
         /\ UNCHANGED << initialTower, pillars >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 


=============================================================================
\* Modification History
\* Last modified Wed Mar 20 10:10:54 CET 2024 by jeujeus
\* Created Wed Mar 20 09:29:51 CET 2024 by jeujeus
