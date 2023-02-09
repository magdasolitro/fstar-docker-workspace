module Exercises

(* signature: it describes the types of the function, i.e. what input type it
accepts and what output type it returns *)
val max (x:int) (y:int) : int 

(* maximum between two integers (we don't specify the types of the arguments,
as they are already specified in the signature) *)
let max x y 
    = if x > y then x else y

let max2 (x:int) (y:int) 
    : z:int{ z = max x y }
    = if x > y then x else y