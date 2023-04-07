module IntFunctions

open FStar.Mul

(* What are some other correct types you can give to factorial? Try
writing them and see if F* agrees with you. Try describing in words
what each of those types mean. *)

val factorial: x:int{x>=0} -> Tot int
let rec factorial n = if n = 0 then 1 else n * (factorial (n - 1))

(* In the tutorial, we proved the claim factorial n >= n, using a Lemma.
   Now, prove the same property without using a Lemma, i.e., specify
   it in the type of factorial.
   Hint: for this to work you need to strengthen the refinement of the
   result. Replace the question mark with the correct formula.

   val factorial: x:nat -> Tot (y:int{y >= x /\ ? })
*)


(* Give several types for the fibonacci function. *)
let rec fibonacci_ty n =
  	if n <= 1 then 1 else fibonacci_ty (n - 1) + fibonacci_ty (n - 2)

val fibonacci : nat -> Tot nat

let rec fibonacci n =
  	if n <= 1 then 1 else fibonacci (n - 1) + fibonacci (n - 2)


(* Prove the following property for the fibonacci function: *)
val fibonacci_greater_than_arg : n:nat{n >= 2} -> Lemma (fibonacci n >= n)

let fibonacci_greater_than_arg n = 
  	admit () (* replace this admit by a real proof *)

// ----------------------------------------------------------------------------
(* Come up with at least three (substantially) different decreases clauses for 
the following function *)

// why do these work?? (decreases %[x;y]) (decreases %[y;x])
val gcd: (x:nat{x>0}) -> (y: nat{y > 0}) -> Tot (r: nat{r > 0}) (decreases %[x;y])

let rec gcd x y = 
  	if x = y 
    	then x 
    else (
      	if (x > y) 
 			then ( gcd (x-y) y)
 	else gcd x (y-x))


val sum_rec: (n:nat) -> Tot nat (decreases n)

let rec sum_rec n = 
  if n > 0 then n + sum_rec (n-1) else 0


val sum_tot: (n:nat) -> Tot nat (decreases n)

let sum_tot n = ((n+1) * n) / 2


(* Prove the following property for the function sum_rec: *)

val sum_rec_correct: (n:nat) ->
	Lemma (sum_rec n = sum_tot n)

let rec sum_rec_correct n =
  	if n = 0 then ()
	else sum_rec_correct(n-1)


val sumup: (n:int) -> (m:int{m>=n}) -> Tot int (decreases (m - n))

let rec sumup n m = 
  	if m = n then n 
	else m + sumup n (m-1)

(* Prove the following Lemma *)

val sum_rec_sumup: (n:nat) -> 
	Lemma (sum_rec n = sumup 0 n)

// base case n = 1 doesn't work, bc we cannot reach the base case of sumup
// where n=0
let rec sum_rec_sumup n =
	if n = 0 then ()
	else sum_rec_sumup (n-1)	// if arg is expression, enclose it in brackets


(* Prove the following Lemma *)
val sumup_seq: (n:int) -> (m:int) -> (k:int) ->
  	Lemma (requires (n <= m /\ (2*m) <= k))
		(ensures (sumup n k = sumup n m + sumup m k-m)) 
		(decreases (k-m))

