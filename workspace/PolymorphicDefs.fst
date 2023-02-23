module PolymorphicDefs

val apply (a b : Type) (f : a -> b) : a -> b
let apply a b f = fun x -> f(x)

val compose (a b c : Type) (f : b -> c) (g : a -> b) : a -> c
let compose a b c f g = fun x -> f(g(x))

val twice (a:Type) (f:a->a) (x:a) : a
let twice a f x = compose a a a f f x

(* 
The signature of apply declares the TYPES involved in the apply function.
In input, apply takes (1) two generic types, a and b, and (2) a function
from a to b.
The return type is an arrow type, a function from a to b

The definition of apply specifies the implementation of the function: apply
takes in input 3 arguments (two types, a and b, and a function, f); the return
type is a function (fun) that takes in input a generic x and returns f(x).

NOTE: if the return type is an arrow type, the function definition will start 
with the keyword "fun" (even though there's really nothing fun in this...).
*)