module Project2

open FStar.List.Tot

(* opcodes of the simplified bytecode fragment *) 
type opcode = 
  | ADD : opcode
  | CALL : opcode
  | AND : opcode
  | LE : opcode
  | PUSH : int -> opcode
  | POP : opcode
  | MLOAD : opcode
  | MSTORE : opcode
  | SLOAD : opcode
  | SSTORE : opcode
  | TIMESTAMP : opcode
  | BALANCE : opcode
  | INPUT : opcode
  | ADDRESS : opcode
  | GAS : opcode
  | JUMP : nat -> opcode
  | JUMPI : nat -> opcode
  | RETURN : opcode
  | STOP : opcode 
  | FAIL : opcode


(* Small step configurations. For simplicity we assume all values (in particular stack and memory values as well as memory and storage addresses) to be represented as integers *) 

type address = int 
(* a contract is a tuple of a an address and its code *) 
type contract = address * list opcode
(* accounts are tuples of the form (b, stor, code) where b is the account's balance, stor is the account's persistent storage, and code is it's opcode *) 
type account = nat * (int -> int) * list opcode
(* the global state is a mapping from contract addresses to accounts *) 
type gstate = address -> Tot account 
(* execution environments are tuples of the form: (actor, input, code) where actor is the address of the active account, input is the input to the call and code is the code currently executed *) 
type exenv = address * int * list opcode 
(* machine states are tuples of the form: (gas, pc, m, s) where gas is the remaining gas, pc is the program counter, memory is the local memory and s is the machine stack *)
type mstate = nat * nat * (int -> int) * list int // does not carry gas 
(* a regular execution state is a tuple of the form (mu, iota, sigma) where mu is the machine state, iota is the execution environment and gstate is the global state *)
type regstate = mstate * exenv * gstate 
(* the transaction environment only carries the blocktimestamp represented as an integer *) 
type tenv = int

(* terminating states are either exception states or halting states of the form (sigma, d, gas) where sigma is the global state at the point of halting, d the return value of the call and gas the remaining gas at the point of halting*)
noeq type terstate = 
| HaltState: gstate -> int -> nat -> terstate
| ExcState: terstate

(* callstacks *)
type plaincallstack = list regstate
noeq type callstack = 
| Ter : terstate -> plaincallstack -> callstack 
| Exec : plaincallstack -> callstack 

(* Small step function *)

(* Polymorphic update function *) 
val update: (#a:eqtype) -> (f: a -> 'b) -> (p:a) -> (e: 'b) -> (x: a) -> Tot 'b 
let update (#a:eqtype) (f: a -> 'b) (p: a) (e: 'b) = 
  fun x -> if x = p then e else f x 

(* size of callstacks *) 
val size: callstack -> Tot nat 
let size (cs: callstack) = 
  match cs with 
   | Exec ps -> length ps 
   | Ter ts ps -> 1 + length ps 

(* a function that extracts the current opcode given the code and a pc *)
val getOpcode: list opcode -> nat -> Tot opcode
let getOpcode code i = 
  match (nth code i) with 
  | None -> STOP
  | Some oc -> oc 

(* a function checking whether a state is a call state. We characterize call states as state where CALL was executed and sufficiently many arguments where on the stack *)
val isCallState: regstate -> Tot bool
let isCallState rs = 
  match rs with 
  | ((gas, pc, m, to:: v:: inp:: resaddr:: stack), (actor, input, code), sigma) -> getOpcode code pc = CALL
  | _ -> false

(* Wellformedness definition: a callstack is well-formed if all of it's non top elements are call states *) 
val wellformed: callstack -> Tot bool 
let wellformed (cs: callstack) =
  match cs with 
  | Exec [] -> false
  | Ter ts ps -> for_all (fun rs -> (isCallState rs)) ps 
  | Exec (s::ps) -> for_all (fun rs -> (isCallState rs)) ps

(* Type for the outcome of a single execution step: either the execution terminated (Stop) as a final state is reached or further execution steps are possible *)
noeq type step_outcome = 
  | Stop : (cs: callstack) -> step_outcome
  | Next : (cs: callstack) -> step_outcome 

(* Auxiliary function for applying the effects of terminated states to the underneath execution states *) 
val apply_returneffects: (ts: terstate) -> (rs: regstate{isCallState rs}) -> Tot regstate
let apply_returneffects ts rs  = 
  let ((gas, pc, mem, to:: v:: imp:: resaddr:: stack), (actor, code, input), gs) = rs
  in assert (pc >= 0); 
    match ts with 
    | ExcState -> ((0, pc+1, mem, 0::stack), (actor, code, input), gs)
    | HaltState gs' res gas' -> ((gas', pc+1, update mem resaddr res, 1::stack), (actor, code, input), gs')

(* 2.1: Small-step semantics *) 

(* Small step function that describes one step of execution. Replace all occurences of 'magic ()', by the definitions as specified in the paper semantics *)
val step: tenv -> cs: callstack {wellformed cs} -> Tot step_outcome
let step te cs  = 
  match cs with 
  | Ter ts [] -> Stop (Ter ts [])  
  | Ter ts (s :: ps) -> Next (Exec ((apply_returneffects ts s)::ps))
  | Exec (s :: ps) -> 
	 let (((gas, pc, mem, stack), (actor, input, code), gs)) = s in 
	   if gas < 1 then Next (Ter ExcState ps)
	   else 
	     match (getOpcode code pc, stack) with 
	     | (ADD, a::b::stack') -> Next (Exec(((gas-1, pc+1, mem, (a+b):: stack'), (actor, input, code), gs) :: ps))
	     | (AND, a::b::stack') -> magic () 
	     | (LE, a::b::stack') -> magic ()
	     | (PUSH x, stack') -> Next (Exec(((gas-1, pc+1, mem, x::stack'), (actor, input, code), gs)::ps))
	     | (POP, x::stack') -> magic () 
	     | (MSTORE, p::v::stack') -> Next (Exec(((gas-1, pc+1, update mem p v, stack'), (actor, input, code), gs)::ps))
	     | (MLOAD, p::stack') ->  magic () 
	     | (SSTORE, p::v::stack') -> magic () 
	     | (SLOAD, v::stack') -> Next (Exec(((gas-1, pc+1, mem, (let (bal, stor, code) = gs actor in stor v)::stack'), (actor, input, code), gs)::ps))
	     | (BALANCE, a::stack') -> magic ()
	     | (ADDRESS, stack') -> Next (Exec(((gas-1, pc+1, mem, actor::stack'), (actor, input, code), gs)::ps))
	     | (INPUT, stack') -> magic () 
	     | (GAS, stack') -> Next (Exec(((gas-1, pc+1, mem, gas::stack'), (actor, input, code), gs)::ps))
	     | (JUMP i, stack') -> Next (Exec((((gas-1, i, mem, stack'), (actor, input, code), gs))::ps))
	     | (JUMPI i, b::stack') -> magic () 
	     | (RETURN, v::stack') -> magic () 
	     | (STOP, stack') -> Next (Ter (HaltState gs 0 (gas-1)) ps) 
	     | (TIMESTAMP, stack') -> magic () 
	     | (CALL, to::v::inp::resaddr::stack') -> magic () 
	     | _ -> Next (Ter ExcState ps) 

(* A simple wrapper for the step function that removes the execution outcome *)
val step_simp: (te: tenv) -> (cs: callstack {wellformed cs}) -> Tot (cs': callstack{wellformed cs'}) 
let step_simp te cs = 
  match (step te cs) with 
  | Next cs' -> cs'
  | Stop cs' -> cs'

(* Bounded step function that executes an execution state for (at most) n execution steps *) 
val nsteps: (n: nat) -> (te: tenv) -> (cs:callstack{wellformed cs}) -> Tot (cs:callstack{wellformed cs}) 
let rec nsteps n te cs = 
  if n=0 then cs 
  else 
    nsteps (n-1) te (step_simp te cs) 

(* 2.2: Termination *) 
(* We will define an interpreter function steps that executes the small step function till reaching a final state (indicated by Stop) *)
(* Our goal is to prove the termination of this function *)
(* To this end, define a function the following function on callstacks that assigns a measure (in terms of a list of naturals that gets lexicographically interpreted) to each call stack *) 

val getDecArgTup: (cs: callstack {wellformed cs}) -> Tot (nat * nat * nat)
let getDecArgTup (cs: callstack {wellformed cs}) = 
 magic ()

let fst3 (a,b,c) = a
let snd3 (a,b,c) = b
let thd3 (a,b,c) = c

(* Interpreter function that executes the small step function till termination *) 
(* Define the function getDecArgTup, shuch that the given decreases clause is sufficient for proving the terminination of the function on all arguments *) 
val steps: (te:tenv) -> (cs:callstack {wellformed cs}) -> Tot callstack (decreases %[fst3 (getDecArgTup cs); snd3 (getDecArgTup cs); thd3 (getDecArgTup cs)]) 
let rec steps te cs = 
  match (step te cs) with 
  | Next cs' -> steps te cs' 
  | Stop cs' -> cs'

(* 2.3: Final states *) 

(* A syntactic characterization of final call stacks (similiar to stopping criterion in step) *) 
val isFinal: (cs: callstack) -> Tot bool
let isFinal cs = 
  match cs with 
  | Ter ts [] -> true
  | _ -> false 

(* Prove that the syntactic characterization of final states implies a semantic characterization (namely that the execution of arbitrary steps does not affect the callstack anymore) *) 
val nsteps_stop: (n: nat) -> (te:tenv) -> (cs: callstack{wellformed cs}) ->
Lemma (requires (isFinal cs))
      (ensures (nsteps n te cs == cs))
let rec nsteps_stop n te cs = 
 admit () 

(* Prove that if a call stack does not change within one step then it must be final. Formulate first the Lemma and then prove it *)
(* val progress: *)

(* 2.4: Uniqueness of callstack *) 

(* Prove that during an execution, every callstack is unique. To this end, first prove that callstacks are always decreasing within n > 0 execution steps (unless they are final) *) 
(* Hint: Use the notion of 'smaller' that you used for proving the termination of steps *)
val order_decreases: (n: nat) -> (te: tenv) -> (cs: callstack{wellformed cs}) -> (cs': callstack) -> 
Lemma (requires (nsteps n te cs == cs' /\ n > 0 /\ ~ (isFinal cs) ))
      (ensures (let x, y, z = getDecArgTup cs' in let x', y', z' = getDecArgTup cs in x < x' \/ x = x' /\ y < y' \/ x=x' /\ y=y' /\ z<z'))
let rec order_decreases n te cs cs' = 
  admit () 

(* Use the previous Lemma to show that the callstacks during execution are unique *) 
val callstacks_unique: (n: nat) -> (te: tenv) -> (cs: callstack{wellformed cs}) -> (cs': callstack) -> 
Lemma (requires (nsteps n te cs == cs' /\ n > 0 /\ ~ (isFinal cs) ))
      (ensures (~ (cs == cs')))
let callstacks_unique n te cs cs' = 
  admit () 

(* 2.5: Exception propagation *) 

(* Prove that when an exception occurs the execution will terminate within 2 * size cs steps *) 
val exception_prop: (te:tenv) -> (ps:plaincallstack) -> 
Lemma (requires (wellformed (Ter ExcState ps)))
      (ensures (nsteps (op_Multiply 2 (length ps)) te (Ter ExcState ps) == (Ter ExcState []))) 
let rec exception_prop te ps = 
  admit () 
