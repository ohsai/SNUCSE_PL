(*
 * SNU 4190.310 Programming Languages 
 * Homework "Exceptions are sugar" Skeleton
 *)

open Xexp

(* TODO : Implement this function *)
type except_env = (int * xexp) list
let empty_except_env = []

let rec except_env_remove_exn : (except_env * xexp) -> xexp = fun (env_in, e_in) -> 
	match e_in with
	|Raise e_sub -> 
		(
		match e_sub with
		|Num n -> snd( List.find (fun (c,_) -> if(c = n) then true else false) env_in)
		|_ -> raise (TypeError (1))
		)
	|Handle (e_sub_1,n_sub,e_sub_2) ->
		(
		let env_new = (n_sub, except_env_remove_exn (env_in,e_in)) :: env_in 
		in
		except_env_remove_exn (env_new, e_sub_1)
		)
	|Equal (e_sub_1, e_sub_2) ->
		(
		Equal(except_env_remove_exn e_sub_1, except_env_remove_exn e_sub_2)
		)
	|If (e_sub_1,e_sub_2,e_sub_3) ->
		(
		If(except_env_remove_exn e_sub_1, except_env_remove_exn e_sub_2, except_env_remove_ e_sub_3)
		)
	|App (e_sub_1,e_sub_2) ->
		(
		App(except_env_remove_exn e_sub_1, except_env_remove_exn e_sub_2)
		)
	|Fn (x, e_sub_1) ->
		(
		Fn(x,except_env_remove_exn e_sub_1)
		)
	|_ -> e_in
		


let removeExn : xexp -> xexp = fun e ->
  except_env_remove_exn(empty_except_env,e)
