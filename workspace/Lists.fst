module Lists

let rec length #a (l:list a)
    : nat
    = match l with
        | [] -> 0
        | _ :: tl -> 1 + length tl

let rec append l1 l2
    = match l1 with
        | [] -> l2
        | hd :: tl -> hd :: append tl l2 
 
val append (#a:Type)(l1 l2:list a) : 
    l:list a{length l = length l1 + length l2}