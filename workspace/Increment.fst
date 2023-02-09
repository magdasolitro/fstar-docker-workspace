module Increment

(* simple definition *) 
//let incr (x:int) : int = x+1

(* refine the return type *)
//let incr (x:int) : y:int { y > x} = x+1

(* return type is a natural number --> returns a subtyping error *)
let incr (x:int) : nat = x+1

