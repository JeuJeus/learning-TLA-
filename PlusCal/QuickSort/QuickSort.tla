----------------------------- MODULE QuickSort -----------------------------
EXTENDS Sequences, Integers, TLC

CONSTANT listLength
ASSUME listLength \in Nat

(*--fair algorithm quicksort {
    variables
        indices = 0..listLength,
        values = indices,
        listToSort \in [indices -> values],
        partitionIndex = -1;
     
    procedure partition(low = 0,high = 0)
    variable 
        pivot = listToSort[high],
        i = (low-1);   
        j = low;
        swapTemp = -1;
    {
        while(j<high) {
            if(listToSort[j] <= pivot) {
                i := i+1;
                swapTemp := listToSort[i];
                listToSort[i] := listToSort[j];
                listToSort[j] := swapTemp;
            };
            j := j+1;
        };
            
        swapTemp := listToSort[i+1];
        listToSort[i+1] := listToSort[high];
        listToSort[high] := swapTemp;
        
        partitionIndex := i+1;
        return;
    }
     
    procedure quickSort(low = 0,high = 0)
    {
        if(low < high) {
            call partition(low,high);
            call quickSort(low, partitionIndex-1);
            call quickSort(partitionIndex+1, high);
        };
        return;
    }   
    
     
    {
        call quickSort(0, listLength);
        assert \A x \in 0..(listLength-1) : listToSort[x] <= listToSort[x+1];
    }

}*)
\* BEGIN TRANSLATION (chksum(pcal) = "62fb6ce4" /\ chksum(tla) = "3182fe21")
\* Parameter low of procedure partition at line 14 col 25 changed to low_
\* Parameter high of procedure partition at line 14 col 33 changed to high_
VARIABLES indices, values, listToSort, partitionIndex, pc, stack, low_, high_, 
          pivot, i, j, swapTemp, low, high

vars == << indices, values, listToSort, partitionIndex, pc, stack, low_, 
           high_, pivot, i, j, swapTemp, low, high >>

Init == (* Global variables *)
        /\ indices = 0..listLength
        /\ values = indices
        /\ listToSort \in [indices -> values]
        /\ partitionIndex = -1
        (* Procedure partition *)
        /\ low_ = 0
        /\ high_ = 0
        /\ pivot = listToSort[high_]
        /\ i = (low_-1)
        /\ j = low_
        /\ swapTemp = -1
        (* Procedure quickSort *)
        /\ low = 0
        /\ high = 0
        /\ stack = << >>
        /\ pc = "Lbl_9"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF j<high_
               THEN /\ IF listToSort[j] <= pivot
                          THEN /\ i' = i+1
                               /\ swapTemp' = listToSort[i']
                               /\ listToSort' = [listToSort EXCEPT ![i'] = listToSort[j]]
                               /\ pc' = "Lbl_2"
                          ELSE /\ pc' = "Lbl_3"
                               /\ UNCHANGED << listToSort, i, swapTemp >>
               ELSE /\ swapTemp' = listToSort[i+1]
                    /\ listToSort' = [listToSort EXCEPT ![i+1] = listToSort[high_]]
                    /\ pc' = "Lbl_4"
                    /\ i' = i
         /\ UNCHANGED << indices, values, partitionIndex, stack, low_, high_, 
                         pivot, j, low, high >>

Lbl_3 == /\ pc = "Lbl_3"
         /\ j' = j+1
         /\ pc' = "Lbl_1"
         /\ UNCHANGED << indices, values, listToSort, partitionIndex, stack, 
                         low_, high_, pivot, i, swapTemp, low, high >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ listToSort' = [listToSort EXCEPT ![j] = swapTemp]
         /\ pc' = "Lbl_3"
         /\ UNCHANGED << indices, values, partitionIndex, stack, low_, high_, 
                         pivot, i, j, swapTemp, low, high >>

Lbl_4 == /\ pc = "Lbl_4"
         /\ listToSort' = [listToSort EXCEPT ![high_] = swapTemp]
         /\ partitionIndex' = i+1
         /\ pc' = Head(stack).pc
         /\ pivot' = Head(stack).pivot
         /\ i' = Head(stack).i
         /\ j' = Head(stack).j
         /\ swapTemp' = Head(stack).swapTemp
         /\ low_' = Head(stack).low_
         /\ high_' = Head(stack).high_
         /\ stack' = Tail(stack)
         /\ UNCHANGED << indices, values, low, high >>

partition == Lbl_1 \/ Lbl_3 \/ Lbl_2 \/ Lbl_4

Lbl_5 == /\ pc = "Lbl_5"
         /\ IF low < high
               THEN /\ /\ high_' = high
                       /\ low_' = low
                       /\ stack' = << [ procedure |->  "partition",
                                        pc        |->  "Lbl_6",
                                        pivot     |->  pivot,
                                        i         |->  i,
                                        j         |->  j,
                                        swapTemp  |->  swapTemp,
                                        low_      |->  low_,
                                        high_     |->  high_ ] >>
                                    \o stack
                    /\ pivot' = listToSort[high_']
                    /\ i' = (low_'-1)
                    /\ j' = low_'
                    /\ swapTemp' = -1
                    /\ pc' = "Lbl_1"
               ELSE /\ pc' = "Lbl_8"
                    /\ UNCHANGED << stack, low_, high_, pivot, i, j, swapTemp >>
         /\ UNCHANGED << indices, values, listToSort, partitionIndex, low, 
                         high >>

Lbl_6 == /\ pc = "Lbl_6"
         /\ /\ high' = partitionIndex-1
            /\ low' = low
            /\ stack' = << [ procedure |->  "quickSort",
                             pc        |->  "Lbl_7",
                             low       |->  low,
                             high      |->  high ] >>
                         \o stack
         /\ pc' = "Lbl_5"
         /\ UNCHANGED << indices, values, listToSort, partitionIndex, low_, 
                         high_, pivot, i, j, swapTemp >>

Lbl_7 == /\ pc = "Lbl_7"
         /\ /\ high' = high
            /\ low' = partitionIndex+1
            /\ stack' = << [ procedure |->  "quickSort",
                             pc        |->  "Lbl_8",
                             low       |->  low,
                             high      |->  high ] >>
                         \o stack
         /\ pc' = "Lbl_5"
         /\ UNCHANGED << indices, values, listToSort, partitionIndex, low_, 
                         high_, pivot, i, j, swapTemp >>

Lbl_8 == /\ pc = "Lbl_8"
         /\ pc' = Head(stack).pc
         /\ low' = Head(stack).low
         /\ high' = Head(stack).high
         /\ stack' = Tail(stack)
         /\ UNCHANGED << indices, values, listToSort, partitionIndex, low_, 
                         high_, pivot, i, j, swapTemp >>

quickSort == Lbl_5 \/ Lbl_6 \/ Lbl_7 \/ Lbl_8

Lbl_9 == /\ pc = "Lbl_9"
         /\ /\ high' = listLength
            /\ low' = 0
            /\ stack' = << [ procedure |->  "quickSort",
                             pc        |->  "Lbl_10",
                             low       |->  low,
                             high      |->  high ] >>
                         \o stack
         /\ pc' = "Lbl_5"
         /\ UNCHANGED << indices, values, listToSort, partitionIndex, low_, 
                         high_, pivot, i, j, swapTemp >>

Lbl_10 == /\ pc = "Lbl_10"
          /\ Assert(\A x \in 0..(listLength-1) : listToSort[x] <= listToSort[x+1], 
                    "Failure of assertion at line 52, column 9.")
          /\ pc' = "Done"
          /\ UNCHANGED << indices, values, listToSort, partitionIndex, stack, 
                          low_, high_, pivot, i, j, swapTemp, low, high >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == partition \/ quickSort \/ Lbl_9 \/ Lbl_10
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Wed Mar 13 09:06:18 CET 2024 by jeujeus
\* Created Tue Mar 12 18:38:34 CET 2024 by jeujeus
