----------------------------- MODULE QuickSort -----------------------------
EXTENDS Sequences, Integers, TLC

CONSTANT listLength
ASSUME listLength \in Nat

(*--algorithm quicksort {
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
    variable pivot = -1;
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
\* BEGIN TRANSLATION (chksum(pcal) = "9118f5ba" /\ chksum(tla) = "2f45a242")
\* Procedure variable pivot of procedure partition at line 16 col 9 changed to pivot_
\* Parameter low of procedure partition at line 14 col 25 changed to low_
\* Parameter high of procedure partition at line 14 col 33 changed to high_
VARIABLES indices, values, listToSort, partitionIndex, pc, stack, low_, high_, 
          pivot_, i, j, swapTemp, low, high, pivot

vars == << indices, values, listToSort, partitionIndex, pc, stack, low_, 
           high_, pivot_, i, j, swapTemp, low, high, pivot >>

Init == (* Global variables *)
        /\ indices = 0..listLength
        /\ values = indices
        /\ listToSort \in [indices -> values]
        /\ partitionIndex = -1
        (* Procedure partition *)
        /\ low_ = 0
        /\ high_ = 0
        /\ pivot_ = listToSort[high_]
        /\ i = (low_-1)
        /\ j = low_
        /\ swapTemp = -1
        (* Procedure quickSort *)
        /\ low = 0
        /\ high = 0
        /\ pivot = -1
        /\ stack = << >>
        /\ pc = "Lbl_9"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF j<high_
               THEN /\ IF listToSort[j] <= pivot_
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
                         pivot_, j, low, high, pivot >>

Lbl_3 == /\ pc = "Lbl_3"
         /\ j' = j+1
         /\ pc' = "Lbl_1"
         /\ UNCHANGED << indices, values, listToSort, partitionIndex, stack, 
                         low_, high_, pivot_, i, swapTemp, low, high, pivot >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ listToSort' = [listToSort EXCEPT ![j] = swapTemp]
         /\ pc' = "Lbl_3"
         /\ UNCHANGED << indices, values, partitionIndex, stack, low_, high_, 
                         pivot_, i, j, swapTemp, low, high, pivot >>

Lbl_4 == /\ pc = "Lbl_4"
         /\ listToSort' = [listToSort EXCEPT ![high_] = swapTemp]
         /\ partitionIndex' = i+1
         /\ pc' = Head(stack).pc
         /\ pivot_' = Head(stack).pivot_
         /\ i' = Head(stack).i
         /\ j' = Head(stack).j
         /\ swapTemp' = Head(stack).swapTemp
         /\ low_' = Head(stack).low_
         /\ high_' = Head(stack).high_
         /\ stack' = Tail(stack)
         /\ UNCHANGED << indices, values, low, high, pivot >>

partition == Lbl_1 \/ Lbl_3 \/ Lbl_2 \/ Lbl_4

Lbl_5 == /\ pc = "Lbl_5"
         /\ IF low < high
               THEN /\ /\ high_' = high
                       /\ low_' = low
                       /\ stack' = << [ procedure |->  "partition",
                                        pc        |->  "Lbl_6",
                                        pivot_    |->  pivot_,
                                        i         |->  i,
                                        j         |->  j,
                                        swapTemp  |->  swapTemp,
                                        low_      |->  low_,
                                        high_     |->  high_ ] >>
                                    \o stack
                    /\ pivot_' = listToSort[high_']
                    /\ i' = (low_'-1)
                    /\ j' = low_'
                    /\ swapTemp' = -1
                    /\ pc' = "Lbl_1"
               ELSE /\ pc' = "Lbl_8"
                    /\ UNCHANGED << stack, low_, high_, pivot_, i, j, swapTemp >>
         /\ UNCHANGED << indices, values, listToSort, partitionIndex, low, 
                         high, pivot >>

Lbl_6 == /\ pc = "Lbl_6"
         /\ /\ high' = partitionIndex-1
            /\ low' = low
            /\ stack' = << [ procedure |->  "quickSort",
                             pc        |->  "Lbl_7",
                             pivot     |->  pivot,
                             low       |->  low,
                             high      |->  high ] >>
                         \o stack
         /\ pivot' = -1
         /\ pc' = "Lbl_5"
         /\ UNCHANGED << indices, values, listToSort, partitionIndex, low_, 
                         high_, pivot_, i, j, swapTemp >>

Lbl_7 == /\ pc = "Lbl_7"
         /\ /\ high' = high
            /\ low' = partitionIndex+1
            /\ stack' = << [ procedure |->  "quickSort",
                             pc        |->  "Lbl_8",
                             pivot     |->  pivot,
                             low       |->  low,
                             high      |->  high ] >>
                         \o stack
         /\ pivot' = -1
         /\ pc' = "Lbl_5"
         /\ UNCHANGED << indices, values, listToSort, partitionIndex, low_, 
                         high_, pivot_, i, j, swapTemp >>

Lbl_8 == /\ pc = "Lbl_8"
         /\ pc' = Head(stack).pc
         /\ pivot' = Head(stack).pivot
         /\ low' = Head(stack).low
         /\ high' = Head(stack).high
         /\ stack' = Tail(stack)
         /\ UNCHANGED << indices, values, listToSort, partitionIndex, low_, 
                         high_, pivot_, i, j, swapTemp >>

quickSort == Lbl_5 \/ Lbl_6 \/ Lbl_7 \/ Lbl_8

Lbl_9 == /\ pc = "Lbl_9"
         /\ /\ high' = listLength
            /\ low' = 0
            /\ stack' = << [ procedure |->  "quickSort",
                             pc        |->  "Lbl_10",
                             pivot     |->  pivot,
                             low       |->  low,
                             high      |->  high ] >>
                         \o stack
         /\ pivot' = -1
         /\ pc' = "Lbl_5"
         /\ UNCHANGED << indices, values, listToSort, partitionIndex, low_, 
                         high_, pivot_, i, j, swapTemp >>

Lbl_10 == /\ pc = "Lbl_10"
          /\ Assert(\A x \in 0..(listLength-1) : listToSort[x] <= listToSort[x+1], 
                    "Failure of assertion at line 53, column 9.")
          /\ pc' = "Done"
          /\ UNCHANGED << indices, values, listToSort, partitionIndex, stack, 
                          low_, high_, pivot_, i, j, swapTemp, low, high, 
                          pivot >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == partition \/ quickSort \/ Lbl_9 \/ Lbl_10
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Tue Mar 12 21:16:15 CET 2024 by jeujeus
\* Created Tue Mar 12 18:38:34 CET 2024 by jeujeus
