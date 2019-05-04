(*
 * SNU 4190.310 Programming Languages 2017 Fall
 *  K- Interpreter Skeleton Code
 * DongKwon Lee (dklee@ropas.snu.ac.kr)
 *)

(* Location Signature *)
module type LOC =
sig
  type t
  val base : t
  val equal : t -> t -> bool
  val diff : t -> t -> int
  val increase : t -> int -> t
end

module Loc : LOC =
struct
  type t = Location of int
  let base = Location(0)
  let equal (Location(a)) (Location(b)) = (a = b)
  let diff (Location(a)) (Location(b)) = a - b
  let increase (Location(base)) n = Location(base+n)
end

(* Memory Signature *)
module type MEM = 
sig
  type 'a t
  exception Not_allocated
  exception Not_initialized
  val empty : 'a t (* get empty memory *)
  val load : 'a t -> Loc.t  -> 'a (* load value : Mem.load mem loc => value *)
  val store : 'a t -> Loc.t -> 'a -> 'a t (* save value : Mem.store mem loc value => mem' *)
  val alloc : 'a t -> Loc.t * 'a t (* get fresh memory cell : Mem.alloc mem => (loc, mem') *)
end

(* Environment Signature *)
module type ENV =
sig
  type ('a, 'b) t
  exception Not_bound
  val empty : ('a, 'b) t (* get empty environment *)
  val lookup : ('a, 'b) t -> 'a -> 'b (* lookup environment : Env.lookup env key => content *)
  val bind : ('a, 'b) t -> 'a -> 'b -> ('a, 'b) t  (* id binding : Env.bind env key content => env'*)
end

(* Memory Implementation *)
module Mem : MEM =
struct
  exception Not_allocated
  exception Not_initialized
  type 'a content = V of 'a | U
  type 'a t = M of Loc.t * 'a content list
  let empty = M (Loc.base,[])

  let rec replace_nth = fun l n c -> 
    match l with
    | h::t -> if n = 1 then c :: t else h :: (replace_nth t (n - 1) c)
    | [] -> raise Not_allocated

  let load (M (boundary,storage)) loc =
    match (List.nth storage ((Loc.diff boundary loc) - 1)) with
    | V v -> v 
    | U -> raise Not_initialized

  let store (M (boundary,storage)) loc content =
    M (boundary, replace_nth storage (Loc.diff boundary loc) (V content))

  let alloc (M (boundary,storage)) = 
    (boundary, M (Loc.increase boundary 1, U :: storage))
end

(* Environment Implementation *)
module Env : ENV=
struct
  exception Not_bound
  type ('a, 'b) t = E of ('a -> 'b)
  let empty = E (fun x -> raise Not_bound)
  let lookup (E (env)) id = env id
  let bind (E (env)) id loc = E (fun x -> if x = id then loc else env x)
end

(*
 * K- Interpreter
 *)
module type KMINUS =
sig
  exception Error of string
  type id = string
  type exp =
    | NUM of int | TRUE | FALSE | UNIT
    | VAR of id
    | ADD of exp * exp
    | SUB of exp * exp
    | MUL of exp * exp
    | DIV of exp * exp
    | EQUAL of exp * exp
    | LESS of exp * exp
    | NOT of exp
    | SEQ of exp * exp            (* sequence *)
    | IF of exp * exp * exp       (* if-then-else *)
    | WHILE of exp * exp          (* while loop *)
    | LETV of id * exp * exp      (* variable binding *)
    | LETF of id * id list * exp * exp (* procedure binding *)
    | CALLV of id * exp list      (* call by value *)
    | CALLR of id * id list       (* call by referenece *)
    | RECORD of (id * exp) list   (* record construction *)
    | FIELD of exp * id           (* access record field *)
    | ASSIGN of id * exp          (* assgin to variable *)
    | ASSIGNF of exp * id * exp   (* assign to record field *)    
    | READ of id
    | WRITE of exp
    
  type program = exp
  type memory
  type env
  type value =
    | Num of int
    | Bool of bool
    | Unit
    | Record of (id -> Loc.t)
  val emptyMemory : memory
  val emptyEnv : env
  val run : memory * env * program -> value
end

module K : KMINUS =
struct
  exception Error of string

  type id = string
  type exp =
    | NUM of int | TRUE | FALSE | UNIT
    | VAR of id
    | ADD of exp * exp
    | SUB of exp * exp
    | MUL of exp * exp
    | DIV of exp * exp
    | EQUAL of exp * exp
    | LESS of exp * exp
    | NOT of exp
    | SEQ of exp * exp            (* sequence *)
    | IF of exp * exp * exp       (* if-then-else *)
    | WHILE of exp * exp          (* while loop *)
    | LETV of id * exp * exp      (* variable binding *)
    | LETF of id * id list * exp * exp (* procedure binding *)
    | CALLV of id * exp list      (* call by value *)
    | CALLR of id * id list       (* call by referenece *)
    | RECORD of (id * exp) list   (* record construction *)
    | FIELD of exp * id           (* access record field *)
    | ASSIGN of id * exp          (* assgin to variable *)
    | ASSIGNF of exp * id * exp   (* assign to record field *)
    | READ of id
    | WRITE of exp

  type program = exp

  type value =
    | Num of int
    | Bool of bool
    | Unit
    | Record of (id -> Loc.t)
    
  type memory = value Mem.t
  type env = (id, env_entry) Env.t
  and  env_entry = Addr of Loc.t | Proc of id list * exp * env

  let emptyMemory = Mem.empty
  let emptyEnv = Env.empty

(* MAIN PART *)
  let value_int v =
    match v with
    | Num n -> n
    | _ -> raise (Error "TypeError : not int")

  let value_bool v =
    match v with
    | Bool b -> b
    | _ -> raise (Error "TypeError : not bool")

  let value_unit v =
    match v with
    | Unit -> ()
    | _ -> raise (Error "TypeError : not unit")

  let value_record v =
    match v with
    | Record r -> r
    | _ -> raise (Error "TypeError : not record")

  let lookup_env_loc e x =
    try
      (match Env.lookup e x with
      | Addr l -> l
      | Proc _ -> raise (Error "TypeError : not addr")) 
    with Env.Not_bound -> raise (Error "Unbound")

  let lookup_env_proc e f =
    try
      (match Env.lookup e f with
      | Addr _ -> raise (Error "TypeError : not proc") 
      | Proc (id_list, exp, env) -> (id_list, exp, env))
    with Env.Not_bound -> raise (Error "Unbound")

  let value_equality : value * value -> bool = fun (v1,v2) ->
	match v1 with
	| Num n1 -> (match v2 with
			| Num n2 -> if n1 == n2 then true else false
			| _ -> false )
	| Bool b1 -> (match v2 with
			| Bool b2 -> if b1 == b2 then true else false
			| _ -> false )
	| Unit -> (match v2 with
			| Unit -> true
			| _ -> false )
	| _ -> false
	 
  let value_less : value * value -> bool = fun (v1,v2) ->
	match v1 with
	| Num n1 -> (match v2 with
			| Num n2 -> if n1 < n2 then true else false
			| _ -> false )
	| Bool b1 -> (match v2 with
			| Bool b2 -> if b1 < b2 then true else false
			| _ -> false )
	| Unit -> (match v2 with
			| Unit -> true
			| _ -> false )
	| _ -> false

  let rec eval mem env e = 
    match e with

    | READ x -> 
      let v = Num (read_int()) in
      let l = lookup_env_loc env x in
      (v, Mem.store mem l v)
    | WRITE e ->
      let (v, mem') = eval mem env e in
      let n = value_int v in
      let _ = print_endline (string_of_int n) in
      (v, mem')
    (*| LETV (x, e1, e2) ->
      let (v, mem') = eval mem env e1 in
      let (l, mem'') = Mem.alloc mem' in
      eval (Mem.store mem'' l v) (Env.bind env x (Addr l)) e2
    | ASSIGN (x, e) ->
      let (v, mem') = eval mem env e in
      let l = lookup_env_loc env x in
      (v, Mem.store mem' l v)*)
    | NUM n ->
	(Num n, mem)
    | TRUE ->
	(Bool true, mem)
    | FALSE ->
	(Bool false, mem)
    | UNIT ->
	(Unit,mem)
    | VAR x ->
	let l = lookup_env_loc env x in
	(Mem.load mem l, mem)
    | ADD (e1,e2) ->
	let (n1, mem') = eval mem env e1 in
	let (n2, mem'') = eval mem' env e2 in
	(Num ((value_int n1) +(value_int n2)), mem'')
    | SUB (e1,e2) ->
	let (n1,mem') = eval mem env e1 in
	let (n2,mem'') = eval mem' env e2 in
	(Num ((value_int n1) -(value_int n2)), mem'')
    | MUL (e1,e2) ->
	let (n1,mem') = eval mem env e1 in
	let (n2, mem'') = eval mem' env e2 in
	(Num ((value_int n1) * (value_int n2)), mem'')
    | DIV (e1,e2) ->
	let (n1,mem') = eval mem env e1 in
	let (n2, mem'') = eval mem' env e2 in
	(Num ((value_int n1) /(value_int n2)), mem'')
    | EQUAL (e1,e2) ->
	let (v1,mem') = eval mem env e1 in
	let (v2, mem'') = eval mem' env e2 in
	if value_equality (v1,v2) then (Bool true, mem'')
	else (Bool false, mem'')
    | LESS (e1, e2) ->
	let (n1,mem') = eval mem env e1 in
	let (n2, mem'') = eval mem' env e2 in
	if value_less (n1,n2) then (Bool true, mem'')
	else (Bool false, mem'')
    | NOT e ->
	let (b,mem') = eval mem env e in
	(Bool (not (value_bool b)) , mem')
    | SEQ (e1,e2) ->
	let (v1,mem') = eval mem env e1 in 
	let (v2,mem'') = eval mem' env e2 in (v2,mem'')
    | IF (e, e1, e2) ->
	let (b, mem') = eval mem env e in 
	if value_bool b == true 
	then let (v,mem'') = eval mem' env e1 in (v,mem'') 
	else let (v,mem'') = eval mem' env e2 in (v,mem'')
    | WHILE (e1,e2) ->
	let (b,mem') = eval mem env e1 in 
	if (value_bool b) = false 
	then (Unit, mem') 
	else let (v1,mem1) = eval mem' env e2 in 
	let (v2, mem2) = eval mem1 env (WHILE (e1, e2)) in 
	(v2,mem2)
    | LETV (x, e1, e2) -> 
	let (v,mem') = eval mem env e1 in 
	let (l,mem'') = Mem.alloc(mem') in
	eval (Mem.store mem'' l v) (Env.bind env x (Addr l)) e2 
    | LETF (f, xlist,e1,e2) ->
	let (v,mem') = eval mem (Env.bind env f (Proc (xlist,e1,env))) e2 in (v,mem') 
    | CALLV (f, elist) -> 
	let rec execute_all_exp :  exp list * env * memory -> value list * env * memory = fun (elist, env_in, mem_in) ->
	match elist with
	| h :: t -> 
	(
	let (vl_out, env_out, mem_out) = execute_all_exp (t,env_in, mem_in) in 
	let (v, mem_modified) = eval mem_out env_out h in
	(v :: vl_out, env_out, mem_modified)
	)
	| [] -> ([], env_in, mem_in)
	in
	let
	(xlist, e_fun, env_fun) = lookup_env_proc env f 
	in
	let
	(vlist, env_out, m_n) = execute_all_exp (elist, env, mem) 
	in
	let rec mem_l_alloc : id list * memory ->Loc.t list * memory = fun (id_list_in, mem_in) ->
	match id_list_in  with
	| head_id_list_in :: tail_id_list_in ->
		let 	
		(loc_list_out, mem_out) = mem_l_alloc (tail_id_list_in,mem_in)
		in
		let 
		(loc, mem_modified) = Mem.alloc mem_out
		in
		(loc :: loc_list_out, mem_modified)
	| [] ->([], mem_in)
	in
	let
	(llist, mem_allocated) = mem_l_alloc (xlist, m_n) 
	in
	let rec mem_l_v_store : Loc.t list * value list * memory -> memory = fun (llist_in, vlist_in, mem_in) ->
	match vlist_in with
	|head_vlist_in :: tail_vlist_in ->
		(
		match llist_in with
		|head_llist_in :: tail_llist_in ->
		let 
		 mem_out = mem_l_v_store (tail_llist_in , tail_vlist_in, mem_in)
		in
		Mem.store mem_out head_llist_in head_vlist_in
		|[] -> raise (Error "InvalidArg")
		)
	|[] -> (
		match llist_in with 
		|[] -> mem_in
		|_ -> raise (Error "InvalidArg"))
	in
	let rec env_x_l_bind : id list * Loc.t list * env -> env = fun (xlist_in, llist_in, env_in) ->
	match xlist_in with
	|head_xlist_in :: tail_xlist_in ->
		(
		match llist_in with
		|head_llist_in :: tail_llist_in ->
		let 
		 env_out = env_x_l_bind (tail_xlist_in , tail_llist_in, env_in)
		in
		Env.bind env_out head_xlist_in (Addr head_llist_in)
		|[] -> raise (Error "InvalidArg")
		)
	|[] -> (
		match llist_in with 
		|[] -> env_in
		|_ -> raise (Error "InvalidArg"  ))
	in
	let
	(v', mem') = eval (mem_l_v_store (llist, vlist, mem_allocated)) (Env.bind (env_x_l_bind (xlist, llist, env_fun)) f (Proc (xlist, e_fun,env_fun))) e_fun
	in
	(v',mem')

    | CALLR (f, ylist) ->
	let
	(xlist, e_fun, env_fun) = lookup_env_proc env f
	in
	let rec env_x_l_bind : id list * Loc.t list * env -> env = fun (xlist_in, llist_in, env_in) ->
	match xlist_in with
	|head_xlist_in :: tail_xlist_in ->
		(
		match llist_in with
		|head_llist_in :: tail_llist_in ->
		let 
		 env_out = env_x_l_bind (tail_xlist_in , tail_llist_in, env_in)
		in
		Env.bind env_out head_xlist_in (Addr head_llist_in)
		|[] -> raise (Error "InvalidArg")
		)
	|[] -> (
		match llist_in with 
		|[] -> env_in
		|_ -> raise (Error "InvalidArg"  ))
	in
	let rec env_y_l_lookup : id list * env -> Loc.t list = fun (ylist, env_in) ->
	match ylist with
	|yh::yt -> (lookup_env_loc env_in yh) ::env_y_l_lookup(yt, env_in)
	|[] -> []
	in
	let
	(v,mem') = eval mem (Env.bind (env_x_l_bind (xlist, env_y_l_lookup (ylist, env),env_fun) ) f (Proc (xlist, e_fun, env_fun))) e_fun 
	in
	(v,mem')

    | RECORD xelist ->
	let rec execute_all_exp : (id * exp) list * env * memory -> (id * value) list * env * memory = fun (ielist, env_in, mem_in) ->
	match ielist with
	| h :: t -> 
	(
	let (ivl_out, env_out, mem_out) = execute_all_exp (t,env_in, mem_in) in 
	let (v, mem_modified) = eval mem_out env_out (snd h) in
	(((fst h),v) :: ivl_out, env_out, mem_modified)
	)
	| [] -> ([], env_in, mem_in)
	in
	let rec ivlist_mem_alloc : ((id * value) list * memory) -> ((id * Loc.t) list * memory ) = fun (ivlist_in, mem_in) ->
	match ivlist_in with
	| h :: t -> 
	let (ivlist_tail, mem_out) = ivlist_mem_alloc (t,mem_in) in
	let (new_cell, mem_modified) = Mem.alloc mem_out in
	((fst h, new_cell ) :: (ivlist_tail), Mem.store mem_modified new_cell (snd h))
	| [] -> ([],mem_in)
	in
	let rec iLlist_to_Record : (id * Loc.t) list -> (id -> Loc.t) = fun iLlist_in ->
	match iLlist_in with
	|h :: t -> (
	(fun (id_in : id) -> if ((fst h) = id_in) then (snd h) else ((iLlist_to_Record t) id_in))) 
	|[] -> (fun (input : id) -> (raise (Error "InvalidField")))
	in
	(
	let (ivlist, _,mem_middle) = execute_all_exp( xelist, env, mem) in
	let (iLlist, mem_final) = ivlist_mem_alloc (ivlist,mem_middle) in
	(Record (iLlist_to_Record iLlist), mem_final)
	)
    | FIELD (e,x) ->
	let (r,mem') = eval mem env e in
	(Mem.load mem' ((value_record r)(x)),mem')
    | ASSIGN (x,e) -> 
	let (v,mem') = eval mem env e in
	let l = lookup_env_loc env x in
	(v, Mem.store mem' l v)
    | ASSIGNF (e1,x,e2) -> 
	let (r,mem1) = eval mem env e1 in 
	let (v,mem2) = eval mem1 env e2 in
	let l = (value_record r) (x)  in
	(v,Mem.store mem2 l v)

   | _ -> failwith "Unimplemented" (* TODO : Implement rest of the cases *)

(* END OF MAIN PART *)

  let run (mem, env, pgm) = 
    let (v, _ ) = (eval mem env pgm) in
    v
end
