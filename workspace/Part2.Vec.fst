module Part2.Vec

type vec (a:Type) : nat -> Type =
  | Nil : vec a 0
  | Cons : #n:nat -> hd:a -> tl:vec a n -> vec a (n + 1)

let rec get #a #n (i:nat{i < n}) (v:vec a n)
  : a
  = let Cons hd tl = v in
    if i = 0 then hd
    else get (i - 1) tl


val append (#a:Type) (#n #m:nat) (v1:vec a n) (v2:vec a m) 
  : vec a (n + m)
let rec append #a #n #m (v1:vec a n) (v2:vec a m)
  : vec a (n + m)
  = match v1 with
    | Nil -> v2
    | Cons hd tl -> Cons hd (append tl v2)


let rec split_at #a #n (i:nat{i <= n}) (v:vec a n) 
  : vec a i & vec a (n - i)
  = if i = 0
    then Nil, v 
    else let Cons hd tl = v in
         let l, r = split_at (i - 1) tl in 
         Cons hd l, r
