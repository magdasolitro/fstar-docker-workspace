module Lists2

val length: list 'a -> Tot nat
let rec length l = match l with
	| [] -> 0
  	| _ :: tl -> 1 + length tl


(* Give append a type that proves it always returns a list whose length is the
   sum of the lengths of its arguments. *)
val append (#a:Type) (l1 l2:list a) 
	: l:list a{length l = length l1 + length l2}
let rec append l1 l2 = match l1 with
	| [] -> l2
	| hd :: tl -> hd :: append tl l2

// check whether element x is present in list xs
val mem: #a:eqtype -> x:a -> xs:list a -> Tot bool
let rec mem #a x xs =
	match xs with
	| [] -> false
	| hd :: tl -> hd = x || mem x tl


(* Prove that mem satisfies the following property: *)
// ovvero: controllare se x appartiene a l1 concatenata a l2 equivale a 
// controllare che x sia in l1 o in l2
val append_mem:  #a:eqtype -> l1:list a -> l2:list a -> x:a
    -> Lemma (mem x (append l1 l2) <==> mem x l1 || mem x l2)	
let rec append_mem #a l1 l2 x = 
	match l1 with 
	| [] -> ()	// se l1 è vuota, abbiamo mem x l2 <==> false || mem x l2, trivial
	| hd :: tl -> append_mem #a tl l2 x


(* 'a is a generic type. It's the same as writing (a:Type)
('a -> bool) e' un function type 
filter prende in input una funzione p:'a -> bool e una lista ls
la funzione p viene applicata a tutti gli elementi della lista
l'output e' una lista con tutti gli elementi x tali per cui p(x) = true *)
val filter: ('a -> bool) -> list 'a -> list 'a
let rec filter p ls = 
	match ls with 
	| [] -> []
	| hd::tl -> if (p hd) then hd::(filter p tl) else filter p tl


(* Prove the following Lemma *)
(* PREMESSA: x è presente in ls e p(x) = true
   CONSEGUENZA: x è presente nella lista degli elementi che soddisfano p()
   Se p(x) = true (premessa), allora sarà presente nella lista restituita da filter p ls
*)
val filter_sound: (#a:eqtype) -> (p: (a -> bool)) -> (ls: list a) -> (x: a)
	-> Lemma(mem x ls /\ p x ==> mem x (filter p ls))
let rec filter_sound #a p ls x =
	match ls with
	| [] -> ()		// premessa invalidata, quindi banalmente vero
	| hd :: tl -> filter_sound #a p tl x


(* Prove the following Lemma *)
val filter_id: (#a: eqtype) -> (p: (a -> bool)) -> (ls: list a) -> 
	Lemma (requires (forall x. mem x ls ==> p x))
    	  (ensures (filter p ls = ls))

let rec filter_id #a p ls =
	match ls with 
	| [] -> ()		// lista vuota, quindi l'elemento x non può essere in ls --> premessa falsa, quindi l'intera proposizione risulta banalmente vera
	| hd :: tl -> filter_id #a p tl

(* Prove the following Lemma *)
(* First, fix the type error in the Lemma *)
//NOTA: la keyword "fun" introduce una funzione anonima (o lambda)
val filter_and: (p: ('a -> bool)) -> (q: ('a -> bool)) -> (ls: list 'a) -> 
	Lemma (ensures (filter p (filter q ls)) == (filter (fun x -> if p x then q x else false) ls))

let rec filter_and p q ls =
	match ls with 
	| [] -> ()
	| hd :: tl -> filter_and p q tl


(* Prove the following Lemma *)
(* First, fix the type error in the Lemma *)
// comm = commutativity?
val filter_comm: (p: ('a -> bool)) -> (q: ('a -> bool)) -> (ls: list 'a) -> 
	Lemma (ensures (filter p (filter q ls)) == (filter q (filter p ls)))

let rec filter_comm p q ls =
	match ls with 
	| [] -> ()
	| hd :: tl -> filter_comm p q tl
 

(* Prove the following Lemma *)
val filter_correct: (#a:eqtype) -> (p: (a -> bool)) -> (ls: list a) -> (x: a) ->
Lemma (requires (mem x (filter p ls)))
      (ensures (mem x ls /\ p x))

let rec filter_correct p ls x = 
	match ls with 
	| [] -> ()
	| hd :: tl -> if (p hd) then (if hd=x then () else filter_correct p tl x) 
				  else filter_correct p tl x


(* Prove the following Lemma *)
(* ovvero: se la presenza di y in ls garantisce la presenza di y in ms, e x è 
   presente x è presente in ls filtrato con p(), allora x è presente anche in 
   ms filtrato con p(). 
   Ha senso, perché vuol dire che x soddisfa p, quindi in qualunque lista che 
   venga filtrata con p(), x rimane. *)
val filter_incl: (#a: eqtype) -> (p: (a -> bool)) -> (ls: list a) -> (ms: list a) -> (x: a) -> 
Lemma (requires (forall y. mem y ls ==> mem y ms) /\ mem x (filter p ls))
      (ensures (mem x (filter p ms)))

let filter_incl p ls ms x = 
	filter_correct p ls x; filter_sound p ms x