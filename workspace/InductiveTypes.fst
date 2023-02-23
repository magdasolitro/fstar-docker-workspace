module InductiveTypes

type new_type = 
    | Const1
    | Const2
    | Const3

let type_as_int (x:new_type)
    : int
    = match x with  
        | Const1 -> 1
        | Const2 -> 2
//      | Const3 -> 3