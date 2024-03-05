----------------------------- MODULE SieveOfEratosthenes -----------------------------
EXTENDS Naturals

-----------------------------
(* algorithm Sieve of Eratosthenes is
    input: an integer n > 1.
    output: all prime number from 2 through n.

    let A be an array of Boolean values, indexed by integers 2 to n,
    initially all set to true.
    
    for i = 2, 3, 4, ..., not exceeding √n do
        if A[i] is true
            for j = i2, i2+i, i2+2i, i2+3i, ..., not exceeding n do
                set A[j] := false

    return all i such that A[i] is true. *)
-----------------------------
            
CONSTANT N

-----------------------------

SquareRootForNExists == \E x \in 1..N : x^2 = N

SquareRoot(n) == CHOOSE sqrt \in 1..n : sqrt^2 = n 

-----------------------------

VARIABLES numbers
vars == <<numbers>>

-----------------------------

Init == 
    /\ numbers = 0..N
    /\ SquareRootForNExists

TypeOK ==
    /\ numbers \subseteq Nat

-----------------------------

RemoveIfPresent(i) == 
  /\ i \in numbers
  /\ numbers' = numbers \ {i}

RemoveNonPrimesByMultiplesOf(i) ==   
    LET non_primes == {(i*2)+(i*j) : j \in 0..N}
        non_primes_not_lager_n == {x \in non_primes: x <= N}
    IN \E x \in non_primes_not_lager_n : 
        RemoveIfPresent(x)                                             

Next == \E i \in 2..SquareRoot(N): RemoveNonPrimesByMultiplesOf(i)
    
Spec == Init /\ [][Next]_vars

THEOREM Spec => []TypeOK    

-----------------------------

Divides(k, number) == 
    \/ k % number = 0
    \/ number % k = 0        
                
isNoPrime(number) == \E k \in 2..number-1 : Divides(k, number)

-----------------------------

\* Invariant that gets false when numbers does only contain Primes
NumbersContainsNotOnlyPrimes == \E n \in numbers : isNoPrime(n)

=============================================================================
\* Modification History
\* Last modified Tue Mar 05 16:44:51 CET 2024 by JUFIGGE
\* Created Fri Mar 05 13:15:02 CET 2024 by JeuJeus
