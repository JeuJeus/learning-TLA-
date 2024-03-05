----------------------------- MODULE TicTacToe -----------------------------
EXTENDS Sequences, Integers

\* This module serves to emulate a tic-tac-toe-game

VARIABLES field, current_player
vars == <<field, current_player>>

-----------------------------------------------------------------------------

initial_field_state == "_"
field_states == {initial_field_state,"X","O"}

field_size == {1,2,3}

supported_field == field_size \X field_size \X field_states

-----------------------------------------------------------------------------

players == {"player_one","player_two"}
player_symbol_mapping == [player_one |-> "X", player_two |-> "O"]

NextPlayer == CHOOSE n \in players : n /= current_player

-----------------------------------------------------------------------------

TypeOK == 
    /\ current_player \in players
    /\ field \subseteq  supported_field

Init == 
    /\ current_player = "player_one"
    /\ field = field_size \X field_size \X {initial_field_state}

-----------------------------------------------------------------------------

PlayerSymbol == player_symbol_mapping[current_player]
PlayerSymbolOfPlayer(p) == player_symbol_mapping[p]

PristineField(x,y) == <<x,y,initial_field_state>>
MarkedField(x,y) == <<x,y,PlayerSymbol>>

-----------------------------------------------------------------------------

AllowedToMark(x,y) == \E f \in field : f = PristineField(x,y)

SetMark == 
    \E x,y \in field_size : 
        /\ AllowedToMark(x,y)
        /\ field' = (field \ {PristineField(x,y)}) \cup {MarkedField(x,y)}

Next == 
    /\ current_player' = NextPlayer
    /\ SetMark

-----------------------------------------------------------------------------

Spec == Init /\ [][Next]_vars

THEOREM Spec => []TypeOK

-----------------------------------------------------------------------------

XCoordinate(fieldx) == fieldx[1] 
YCoordinate(fieldy) == fieldy[2]
Value(fieldv) == fieldv[3] 

-----------------------------------------------------------------------------

HorizontalWin == 
    \E x \in field_size, p \in players : 
        LET row == { f \in field : XCoordinate(f) = x}
        IN \A el \in row : Value(el) = PlayerSymbolOfPlayer(p)
        
VerticalWin ==
    \E y \in field_size, p \in players : 
        LET column == { f \in field : YCoordinate(f) = y}
        IN \A el \in column : Value(el) = PlayerSymbolOfPlayer(p)

AllowedDiagonalWinLeftToRightFields(field_left_to_right) == 
    \/ (XCoordinate(field_left_to_right) = 1 /\ YCoordinate(field_left_to_right) = 1) 
    \/ (XCoordinate(field_left_to_right) = 2 /\ YCoordinate(field_left_to_right) = 2) 
    \/ (XCoordinate(field_left_to_right) = 3 /\ YCoordinate(field_left_to_right) = 3)

DiagonalWinLeftToRight == 
    \E p \in players : 
        LET diagonal_left_to_right == { f \in field : AllowedDiagonalWinLeftToRightFields(f)}
        IN \A el \in diagonal_left_to_right : Value(el) = PlayerSymbolOfPlayer(p)

AllowedDiagonalWinRightToLeftFields(field_right_to_left) ==
    \/ (XCoordinate(field_right_to_left) = 1 /\ YCoordinate(field_right_to_left) = 3) 
    \/ (XCoordinate(field_right_to_left) = 2 /\ YCoordinate(field_right_to_left) = 2) 
    \/ (XCoordinate(field_right_to_left) = 3 /\ YCoordinate(field_right_to_left) = 1)

DiagonalWinRightToLeft == 
    \E p \in players :  
        LET diagonal_right_to_left == { f \in field : AllowedDiagonalWinRightToLeftFields(f)}
        IN \A el \in diagonal_right_to_left : Value(el) = PlayerSymbolOfPlayer(p)

DiagonalWin ==
    \/ DiagonalWinLeftToRight
    \/ DiagonalWinRightToLeft

\* set this as an invariant to get informed about game winning moves + player on model checking
GameEnded == 
    /\ HorizontalWin /= TRUE 
    /\ VerticalWin /= TRUE
    /\ DiagonalWin /= TRUE

=============================================================================
\* Modification History
\* Last modified Fri Mar 01 15:42:30 CET 2024 by JUFIGGE
\* Last modified Fri Mar 01 13:14:03 CET 2024 by JeuJeus
\* Created Fri Mar 01 13:14:03 CET 2024 by JeuJeus
