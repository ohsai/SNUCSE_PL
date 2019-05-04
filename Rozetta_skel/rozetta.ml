(*
 * SNU 4190.310 Programming Languages 
 * Homework "Rozetta" Skeleton
 * Dongkwon Lee (dklee@ropas.snu.ac.kr)
 *)

let trans_v : Sm5.value -> Sonata.value = function
  | Sm5.Z z  -> Sonata.Z z
  | Sm5.B b  -> Sonata.B b
  | Sm5.L _ -> raise (Sonata.Error "Invalid input program : pushing location")
  | Sm5.Unit -> Sonata.Unit
  | Sm5.R _ -> raise (Sonata.Error "Invalid input program : pushing record")

(* TODO : complete this function *)
let rec trans_obj : Sm5.obj -> Sonata.obj = function
  | Sm5.Val v -> Sonata.Val (trans_v v)
  | Sm5.Id id -> Sonata.Id id
  | Sm5.Fn (arg, command) -> Sonata.Fn(arg, 
[
	Sonata.MALLOC;Sonata.BIND("call@proc_after");
	Sonata.PUSH(Sonata.Id("call@proc_after"));Sonata.STORE
]
 @	(trans' command) @ 
[	
	Sonata.PUSH(Sonata.Id("call@proc_after"));Sonata.LOAD;
	Sonata.PUSH(Sonata.Val (Sonata.Z 0)); 
	Sonata.MALLOC; 
	Sonata.CALL
]) (* fixed *)

(* TODO : complete this function *)
and trans' : Sm5.command -> Sonata.command = function
  | Sm5.PUSH obj :: cmds -> Sonata.PUSH (trans_obj obj) :: (trans' cmds)
  | Sm5.POP :: cmds -> Sonata.POP :: (trans' cmds)
  | Sm5.STORE :: cmds -> Sonata.STORE :: (trans' cmds)
  | Sm5.LOAD :: cmds -> Sonata.LOAD :: (trans' cmds)
  | Sm5.JTR (c1, c2) :: cmds ->  Sonata.JTR (trans' (c1 @ cmds), trans' (c2 @ cmds)) :: [](* fixed *)
  | Sm5.MALLOC :: cmds -> Sonata.MALLOC :: (trans' cmds)
  | Sm5.BOX z :: cmds -> Sonata.BOX z :: (trans' cmds)
  | Sm5.UNBOX id :: cmds -> Sonata.UNBOX id :: (trans' cmds)
  | Sm5.BIND id :: cmds -> Sonata.BIND id :: (trans' cmds)
  | Sm5.UNBIND :: cmds -> Sonata.UNBIND :: (trans' cmds)
  | Sm5.GET ::cmds -> Sonata.GET :: (trans' cmds)
  | Sm5.PUT ::cmds -> Sonata.PUT :: (trans' cmds)
  | Sm5.CALL :: cmds -> [
	Sonata.PUSH( (Sonata.Fn("call@proc_before_arg",  
trans' cmds @ 
[	
	Sonata.PUSH(Sonata.Id("call@proc_after"));Sonata.LOAD;
	Sonata.PUSH(Sonata.Val (Sonata.Z 0)); 
	Sonata.MALLOC; 
	Sonata.CALL

])));
	Sonata.MALLOC;Sonata.BIND("call@proc_before");
	Sonata.MALLOC;Sonata.BIND("call@arg_loc"); 
	Sonata.MALLOC;Sonata.BIND("call@arg_val");
	Sonata.MALLOC;Sonata.BIND("call@arg_proc"); 
	Sonata.PUSH(Sonata.Id("call@proc_before"));Sonata.STORE;
	Sonata.PUSH(Sonata.Id("call@arg_loc")); Sonata.STORE; 
	Sonata.PUSH(Sonata.Id("call@arg_val")); Sonata.STORE; 
	Sonata.PUSH(Sonata.Id("call@arg_proc")); Sonata.STORE; 
	Sonata.PUSH(Sonata.Id("call@proc_before"));Sonata.LOAD;
	Sonata.PUSH(Sonata.Id("call@arg_proc")); Sonata.LOAD;
	Sonata.PUSH(Sonata.Id("call@arg_val")); Sonata.LOAD;
	Sonata.PUSH(Sonata.Id("call@arg_loc")); Sonata.LOAD;
	Sonata.CALL
	] (* fixed *)
  | Sm5.ADD :: cmds -> Sonata.ADD :: (trans' cmds)
  | Sm5.SUB :: cmds -> Sonata.SUB :: (trans' cmds)
  | Sm5.MUL :: cmds -> Sonata.MUL :: (trans' cmds)
  | Sm5.DIV :: cmds -> Sonata.DIV :: (trans' cmds)
  | Sm5.EQ :: cmds -> Sonata.EQ :: (trans' cmds)
  | Sm5.LESS :: cmds -> Sonata.LESS :: (trans' cmds)
  | Sm5.NOT :: cmds -> Sonata.NOT :: (trans' cmds)
  | [] -> []

(* TODO : complete this function *)
let trans : Sm5.command -> Sonata.command = fun command ->
  	[Sonata.MALLOC ;Sonata.BIND("call@proc_after");Sonata.PUSH(Sonata.Fn("call@proc_after_arg",[]));Sonata.PUSH (Sonata.Id("call@proc_after"));Sonata.STORE]@
	trans'(command)
