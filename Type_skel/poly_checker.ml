(*
 * SNU 4190.310 Programming Languages 2017 Fall
 * Type Checker Skeleton
 *)

open M

type var = string

type typ = 
  | TInt
  | TBool
  | TString
  | TPair of typ * typ
  | TLoc of typ
  | TFun of typ * typ
  | TVar of var
  (* Modify, or add more if needed *)

type typ_scheme =
  | SimpleTyp of typ 
  | GenTyp of (var list * typ)

type typ_env = (M.id * typ_scheme) list

let count = ref 0 

let new_var () = 
  let _ = count := !count +1 in
  "x_" ^ (string_of_int !count)

(* Definitions related to free type variable *)

let union_ftv ftv_1 ftv_2 = 
  let ftv_1' = List.filter (fun v -> not (List.mem v ftv_2)) ftv_1 in
  ftv_1' @ ftv_2
  
let sub_ftv ftv_1 ftv_2 =
  List.filter (fun v -> not (List.mem v ftv_2)) ftv_1

let rec ftv_of_typ : typ -> var list = function
  | TInt | TBool | TString -> []
  | TPair (t1, t2) -> union_ftv (ftv_of_typ t1) (ftv_of_typ t2)
  | TLoc t -> ftv_of_typ t
  | TFun (t1, t2) ->  union_ftv (ftv_of_typ t1) (ftv_of_typ t2)
  | TVar v -> [v]

let ftv_of_scheme : typ_scheme -> var list = function
  | SimpleTyp t -> ftv_of_typ t
  | GenTyp (alphas, t) -> sub_ftv (ftv_of_typ t) alphas 

let ftv_of_env : typ_env -> var list = fun tyenv ->
  List.fold_left 
    (fun acc_ftv (id, tyscm) -> union_ftv acc_ftv (ftv_of_scheme tyscm))
    [] tyenv 

(* Generalize given type into a type scheme *)
let generalize : typ_env -> typ -> typ_scheme = fun tyenv t ->
  let env_ftv = ftv_of_env tyenv in
  let typ_ftv = ftv_of_typ t in
  let ftv = sub_ftv typ_ftv env_ftv in
  if List.length ftv = 0 then
    SimpleTyp t
  else
    GenTyp(ftv, t)

(* Definitions related to substitution *)

type subst = typ -> typ

let empty_subst : subst = fun t -> t

let make_subst : var -> typ -> subst = fun x t ->
  let rec subs t' = 
    match t' with
    | TVar x' -> if (x = x') then t else t'
    | TPair (t1, t2) -> TPair (subs t1, subs t2)
    | TLoc t'' -> TLoc (subs t'')
    | TFun (t1, t2) -> TFun (subs t1, subs t2)
    | TInt | TBool | TString -> t'
  in subs

let (@@) s1 s2 = (fun t -> s1 (s2 t)) (* substitution composition *)

let subst_scheme : subst -> typ_scheme -> typ_scheme = fun subs tyscm ->
  match tyscm with
  | SimpleTyp t -> SimpleTyp (subs t)
  | GenTyp (alphas, t) ->
    (* S (\all a.t) = \all b.S{a->b}t  (where b is new variable) *)
    let betas = List.map (fun _ -> new_var()) alphas in
    let s' =
      List.fold_left2
        (fun acc_subst alpha beta -> make_subst alpha (TVar beta) @@ acc_subst)
        empty_subst alphas betas
    in
    GenTyp (betas, subs (s' t))

let subst_env : subst -> typ_env -> typ_env = fun subs tyenv ->
  List.map (fun (x, tyscm) -> (x, subst_scheme subs tyscm)) tyenv


(* TODO : Implement this function *)
let var_typ_unify : (var * typ) -> subst = fun (v_in, typ_in) ->
	let existence = List.exists (fun c -> if (c = v_in) then true else false) (ftv_of_typ (typ_in)) 
	in
	if (existence) then raise (M.TypeError ("recursive substitution"))
	else (make_subst v_in typ_in)

let rec unify : (typ * typ) -> subst = fun (t_1, t_2) ->
	if(t_1 = t_2) then empty_subst
	else 
	match t_1 with
	|TVar(alpha) ->var_typ_unify(alpha, t_2)
	|TFun(tau_1,tau_2) ->
	(
	match t_2 with
	|TFun(tau'_1, tau'_2) ->
	(
		let s = unify(tau_1, tau'_1) in
		let s' = unify(s tau_2, s tau'_2) in
		(s @@ s')
	)
	|TVar(alpha) -> var_typ_unify(alpha, t_1) 
	|_ -> raise (M.TypeError("fail"))
	)
	|TPair(tau_1, tau_2) ->
	(
	match t_2 with
	|TPair(tau'_1, tau'_2) ->
	(
		let s = unify(tau_1, tau'_1) in
		let s' = unify(s tau_2, s tau'_2) in
		(s @@ s')
	)
	|TVar(alpha) -> var_typ_unify(alpha, t_1) 
	|_ -> raise (M.TypeError("fail"))
	)
	|TLoc (tau) ->
	(
	match t_2 with
	|TLoc (tau') ->
	(
		let s = unify(tau, tau') in
		(s)
	)
	|TVar(alpha) -> var_typ_unify(alpha, t_1) 
	|_ -> raise (M.TypeError("fail"))
	)
	|_ ->
	(
	match t_2 with
	|TVar(alpha) -> var_typ_unify(alpha,t_1)
	|_ -> raise (M.TypeError("fail"))
	)
	 

let rec w_let_polymorphic : (typ_env * M.exp) -> (subst * typ) = fun (gamma, e) ->
	match e with
	| M.CONST c->
	(
	match c with
	|M.S _ ->(empty_subst,TString)
	|M.N _ ->(empty_subst,TInt)
	|M.B _ -> (empty_subst,TBool)
	)
	| M.VAR x ->
	(
	let (_ ,gamma_x) = List.find (fun (id_in,_) -> if (id_in = x) then true else false ) gamma
	in
	let result = subst_scheme empty_subst gamma_x
	in
	let output = 
	(match result with
		|SimpleTyp(tau) -> tau
		|GenTyp(betas, alphas_to_betas_tau) -> alphas_to_betas_tau
	)
	in
	(empty_subst, output)
	)
	| M.FN (x, e)->
	(
	let beta_name = new_var()
	in
	let beta = TVar(beta_name)
	in 
	let (s_1, t_1) = w_let_polymorphic((x,SimpleTyp(beta))::gamma,e)
	in
	(s_1, TFun(s_1 beta,t_1))
	)
	| M.APP (e_1, e_2)->
	(
	let (s_1, t_1) = w_let_polymorphic(gamma,e_1)
	in
	let (s_2, t_2) = w_let_polymorphic((subst_env s_1 gamma),e_2)
	in
	let beta = TVar(new_var())
	in
	let s_3 = unify(s_2 t_1, TFun(t_2, beta)) 
	in
	(s_3 @@ s_2 @@ s_1 , s_3 beta)
	)
	| M.LET (decl_in, e_2)->
	let (x,e_1) = 
	match decl_in with
	|M.REC(f_decl,x_decl,e_decl)->
		(f_decl, M.FN(x_decl,e_decl))
	|M.VAL(f_decl, e_decl)->(f_decl, e_decl)
	in
	let (s_1, t_1) = w_let_polymorphic(gamma,e_1)
	in
	let (s_2, t_2) = w_let_polymorphic((x,generalize (subst_env s_1 gamma) t_1)::(subst_env s_1 gamma),e_2)
	in
	(s_2 @@ s_1, t_2)
	| M.IF(e_1, e_2, e_3) ->
	(
	let (s_1, t_1) = w_let_polymorphic(gamma, e_1)
	in
	let s_1b = unify(TBool,t_1)
	in
	let (s_2, t_2) = w_let_polymorphic(subst_env (s_1b @@ s_1) gamma,e_2 )
	in
	let (s_3, t_3) = w_let_polymorphic(subst_env (s_2 @@ s_1b @@ s_1) gamma,e_3)
	in
	let s_4 = unify(s_3 t_2, t_3)
	in
	(s_4 @@ s_3 @@ s_2 @@ s_1b @@ s_1,s_4 t_3)
	)
	| M.BOP (bop_in, e_1, e_2)->
	(
	let (s_1, t_1) = w_let_polymorphic(gamma, e_1)
	in
	let (s_2, t_2) = w_let_polymorphic(subst_env s_1 gamma , e_2)
	in
	match bop_in with
	|M.ADD | M.SUB ->
	(
	let s_3 = unify(TInt, s_2 t_1)
	in
	let s_4 = unify(TInt, s_3 t_2)
	in
	(s_4 @@ s_3 @@ s_2 @@ s_1 , TInt)
	) (*
	|SUB ->
	(
	let s_3 = unify(TInt, s_2 t_1)
	in
	let s_4 = unify(TInt, s_3 t_2)
	in
	(s_4 @@ s_3 @@ s_2 @@ s_1 , (s_4 @@ s_3) t_2)
	) *)
	|M.EQ ->
	(
	let s_3 = unify(t_2, s_2 t_1)
	in
	(s_3 @@ s_2 @@ s_1 , TBool)
	)
	|_ ->
	(
	let s_3 = unify(TBool, s_2 t_1)
	in
	let s_4 = unify(TBool, s_3 t_2)
	in
	(s_4 @@ s_3 @@ s_2 @@ s_1 , TBool)
	)
	)
	| M.READ -> (empty_subst, TInt)
	| M.WRITE e ->
	(
	let (s_1, t_1) = w_let_polymorphic(gamma,e)
	in
	if(match t_1 with TInt|TBool|TString|TVar _ -> true |_ -> false) 
	then (s_1, t_1)
	else raise (M.TypeError ("write int bool string"))
	)
	| M.MALLOC e->
	(
	let (s_1, t_1) = w_let_polymorphic(gamma, e)
	in
	(s_1,TLoc (t_1))
	)
	| M.BANG e ->
	(
	let (s_1, t_1) = w_let_polymorphic(gamma, e)
	in
	let beta = TVar(new_var()) 
	in
	let s_2 = unify (TLoc(beta),t_1)
	in
	(s_2 @@ s_1, s_2 beta)
	)
	| M.SEQ (e_1,e_2) ->
	(
	let (s_1, t_1) = w_let_polymorphic(gamma, e_1)
	in
	let (s_2, t_2) = w_let_polymorphic(subst_env s_1 gamma, e_2)
	in
	(s_2 @@ s_1,t_2)
	)
	|M.ASSIGN (e_1,e_2) ->
	(
	let (s_1, t_1) = w_let_polymorphic(gamma, e_1)
	in
	let (s_2, t_2) = w_let_polymorphic(subst_env s_1 gamma, e_2) 
	in
	let s_3 = unify(TLoc(t_2),s_2 t_1)
	in
	(s_3 @@ s_2 @@ s_1 , s_3 t_2)
	)
	|M.PAIR (e_1, e_2) ->
	(
	let (s_1, t_1) = w_let_polymorphic(gamma,e_1)
	in
	let (s_2, t_2) = w_let_polymorphic(subst_env s_1 gamma, e_2)
	in
	(s_2 @@ s_1 , TPair(s_2 t_1, t_2))
	)
	|M.FST (e) ->
	(
	let (s_1, t_1) = w_let_polymorphic(gamma, e)
	in
	let beta1 = TVar(new_var())
	in
	let beta2 = TVar(new_var())
	in
	let s_2 = unify(t_1, TPair(beta1, beta2))
	in
	(s_2 @@ s_1 , s_2 beta1)
	)
	|M.SND (e) ->
	(
	let (s_1, t_1) = w_let_polymorphic(gamma, e)
	in
	let beta1 = TVar(new_var())
	in
	let beta2 = TVar(new_var())
	in
	let s_2 = unify(t_1, TPair(beta1, beta2))
	in
	(s_2 @@ s_1 , s_2 beta2)
	)

let rec typ_to_Mtyp : typ -> M.typ = fun (tau_in) ->
	match tau_in with
	|TInt -> M.TyInt
	|TBool -> M.TyBool
	|TString -> M.TyString
	|TPair (a, b) -> M.TyPair (typ_to_Mtyp(a),typ_to_Mtyp(b))
	|TLoc (t) -> M.TyLoc (typ_to_Mtyp(t))
	|_ -> raise (M.TypeError ("typ_to_Mtyp"))

let check : M.exp -> M.typ = fun (exp_in) ->
	let (_, tau) = 	w_let_polymorphic ([], exp_in)
	in
	typ_to_Mtyp(tau)
  (*raise (M.TypeError "Type Checker Unimplemented")*)
