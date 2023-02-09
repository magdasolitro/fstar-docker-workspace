module Factorial2

(* alternative def 1 *)
let rec fac1 (n:nat) : int
    = if n=0 then 1
      else n * fac1(n-1)

(* alternative def 2 *)
let rec fac2(n:nat) : y:int{ y>=1 }
    = if n=0 then 1
      else n * fac2(n-1)