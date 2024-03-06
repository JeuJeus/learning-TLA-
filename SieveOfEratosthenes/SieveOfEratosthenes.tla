----------------------------- MODULE SieveOfEratosthenes -----------------------------
EXTENDS Naturals

-----------------------------
(* algorithm Sieve of Eratosthenes is
    input: an integer n > 1.
    output: all prime number from 2 through n.

    let A be an array of Boolean values, indexed by integers 2 to n,
    initially all set to true.
    
    for i = 2, 3, 4, ..., not exceeding sqrt(n) do
        if A[i] is true
            for j = i2, i2+i, i2+2i, i2+3i, ..., not exceeding n do
                set A[j] := false

    return all i such that A[i] is true. *)
-----------------------------
            
CONSTANT N \* input: an integer n > 1

-----------------------------

SquareRootForNExists == \E x \in 1..N : x^2 = N

SquareRoot(n) == CHOOSE sqrt \in 1..n : sqrt^2 = n 

-----------------------------

VARIABLES numbers, iterator
vars == <<numbers, iterator>>

-----------------------------

Init ==
    /\ numbers = 0..N \* output: all prime number from 2 through n
    /\ iterator = 2..SquareRoot(N) \*let A be an array of Boolean values, indexed by integers 2 to n, initially all set to true.
    /\ SquareRootForNExists

TypeOK ==
    /\ numbers \subseteq Nat
    /\ iterator \subseteq Nat

-----------------------------

GetCurrentNumberFromIterator == CHOOSE i \in iterator : i = i \* trick to choose fixed number instead of iterating all possible combinations

RemoveNonPrimesByMultiplesOf(i) ==   
    LET non_primes == {(i*2)+(i*j) : j \in 0..N} \*for j = i2, i2+i, i2+2i, i2+3i, ...
            non_primes_not_larger_n == {x \in non_primes: x <= N} \*for j = i2, i2+i, i2+2i, i2+3i, ..., not exceeding n do
    IN  numbers' = numbers \ non_primes_not_larger_n

HandleCurrentNumberBasedOnPresenceinNumbers(i) ==
    \/  /\ i \in numbers \*if A[i] is true
        /\ RemoveNonPrimesByMultiplesOf(i)
    \/  numbers' = numbers

Next == LET i == GetCurrentNumberFromIterator \* for i = 2, 3, 4, ..., not exceeding sqrt(n) do
        IN  /\ iterator' = iterator \ {i}
            /\ RemoveNonPrimesByMultiplesOf(i)
    
Spec == Init /\ [][Next]_vars

THEOREM Spec => []TypeOK    

-----------------------------

Divides(k, number) == 
    \/ k % number = 0
    \/ number % k = 0        
                
isNoPrime(number) == \E k \in 2..number-1 : Divides(k, number)

-----------------------------

\* Invariant that gets false when numbers does only contain Primes
NumbersContainsNotOnlyPrimes == \E n \in numbers : isNoPrime(n) \* return all i such that A[i] is true.

=============================================================================
\* Modification History
\* Last modified Wed Mar 06 10:18:51 CET 2024 by JUFIGGE
\* Created Fri Mar 05 13:15:02 CET 2024 by JeuJeus
