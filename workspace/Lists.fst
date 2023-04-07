module Lists

let rec length #a (l:list a)
    : nat
    = match l with
        | [] -> 0
        | _ :: tl -> 1 + length tl

// function signature
val append (#a:Type)(l1 l2:list a) : 
    l:list a{length l = length l1 + length l2}

let rec append l1 l2
    = match l1 with
        | [] -> l2
        | hd :: tl -> hd :: append tl l2 

// lemma: length of output list is equal to the sum of the two starting lists
val app_length (#a:Type) (l1 l2:list a) 
    : Lemma (length (append l1 l2) = length l1 + length l2)

let rec app_length #a l1 l2
    = match l1 with 
        | [] -> ()
        | _ :: tl -> app_length tl l2

val access (#a:Type) (lst:list a) (idx:int{idx > 0}) 
    : a

let access lst idx
	= T?.