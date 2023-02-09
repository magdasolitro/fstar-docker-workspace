module Factorial
open FStar.Mul                  // imports symbol * for multiplication

(* function signature *)
val factorial: nat -> nat

(* function def *)
let rec factorial n =           
    if n = 0 then 1
    else n * factorial (n-1)