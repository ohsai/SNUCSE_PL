exception Error of string

type require = id * (cond list)
and cond
	= Items of gift list
	|Same of id
	|Common of cond * cond
	|Except of cond * gift list
and gift = int
and id = A|B|C|D|E

let shoppingList : require list -> (id * gift list) list = fun req_list_in -> 
	 
	let unwrap identifier = match identifier with
	   | A -> 0
	   | B -> 1
	   | C -> 2
	   | D -> 3
	   | E -> 4
	in
   	let printList lst =
      	print_char '[';
      	List.iteri (fun i -> fun (id, gifts) ->
        	 print_char '(';
         	print_char (Char.chr (65 + unwrap id));
         	print_string ", ";
         	(match gifts with
            	| [] -> print_string "nil";
            	| gl -> print_char '['; List.iteri(fun j -> fun gift ->
               	print_string (string_of_int gift);
               	if (j + 1 != List.length gl) then
                  print_string ", ";
            	) gl; print_char ']');
        	print_string ")";
         	if (i + 1 != List.length lst) then
            	print_string ", ";
      		) lst;
      	print_char ']';
	in

	let formatting_req_list : require list -> require list = fun formatting_req_list_in ->
		let rec search_id_from_reqlist : id * require list -> require = fun (id_in, search_require_list_in) ->
			(*print_endline("formatting_req_list"); *)
			match search_require_list_in with
			| h::t -> if ((fst h) = id_in) then h else search_id_from_reqlist (id_in, t)
			| [] -> (id_in, [])
		in
		search_id_from_reqlist (A,formatting_req_list_in) :: 
		search_id_from_reqlist (B,formatting_req_list_in) :: 
		search_id_from_reqlist (C,formatting_req_list_in) :: 
		search_id_from_reqlist (D,formatting_req_list_in) :: 
		search_id_from_reqlist (E,formatting_req_list_in) :: []		
	in 
	let rec iteration_once : (require list * ((id * (gift list)) list)) -> (id * (gift list)) list  = fun (iter_req_list_in , iter_idgift_list_in) ->
		let req_eval : (require * ((id * gift list) list)) -> id * (gift list)  = fun (reqeval_req_in, reqeval_idgift_list_in)->
			let rec cond_eval : (cond * ((id *  (gift list)) list)) -> gift list = fun (condeval_cond_in, condeval_idgift_list_in) ->
				let rec search_id_from_giftlist : (id * ((id * (gift list)) list)) -> gift list = fun (id_in, search_idgift_list_in) ->
					(* print_endline("search_id_from_giftlist"); *)
					match search_idgift_list_in with
					| h::t -> if ((fst h) = id_in) then (snd h) else search_id_from_giftlist (id_in, t)
					| [] -> raise (Error "id_fail")
				in
				let sort_common_giftlist : ((gift list) * (gift list)) -> gift list = fun (gl1, gl2) ->
					let rec common_giftlist : ((gift list) * (gift list)) -> gift list = fun (com_gl1, com_gl2) ->
						let rec common_gift_from_giftlist : gift * (gift list) -> bool = fun (com_gift, from_giftlist) ->
							match from_giftlist with
							| head :: tail -> if (com_gift = head) then true else common_gift_from_giftlist (com_gift, tail)
							| [] -> false
						in
						match com_gl2 with
						| h:: t -> if (common_gift_from_giftlist (h , com_gl1) ) then h :: common_giftlist(com_gl1, t) else common_giftlist(com_gl1, t)
						| [] -> []
					in
					let ascending_Compare : gift -> gift -> int = fun gl1 gl2 ->
						if (gl1 > gl2) then 1 else (if (gl1 = gl2) then 0 else -1)
					in
					(* print_endline("sort_common_giftlist"); *)
					(List.sort ascending_Compare (common_giftlist (gl1, gl2)))
				in
				let sort_subtract_giftlist : ((gift list * gift list))-> gift list = fun (gl1, gl2) ->
					let rec subtract_giftlist : ((gift list)* (gift list))-> gift list = fun (sub_gl1, sub_gl2) ->
						let rec subtract_gift_from_giftlist : gift * (gift list) -> gift list = fun (ext_gift, from_giftlist) ->
							(* print_endline("subtract_gift_from_giftlist"); *)
							match from_giftlist with
							| head :: tail -> if (ext_gift = head) then subtract_gift_from_giftlist (ext_gift, tail) else head :: subtract_gift_from_giftlist(ext_gift, tail)
							| [] -> []
						in
						match sub_gl2 with
						| h :: t -> subtract_giftlist (subtract_gift_from_giftlist(h, sub_gl1) , t)
						| [] -> sub_gl1
					in	
					let ascending_Compare : gift -> gift -> int = fun gl1 gl2 ->
						if (gl1 > gl2) then 1 else (if (gl1 = gl2) then 0 else -1)
					in
					(* print_endline("sort_subtract_giftlist");*)
					List.sort ascending_Compare (subtract_giftlist (gl1, gl2)) 
				in
				let sort_items_giftlist : (gift list) -> (gift list) = fun items_gl_in ->
					let rec probe_giftlist : (gift list) -> gift list = fun probe_gl_in ->
						let rec g_notin_gl : gift * (gift list) -> bool = fun (g1, gl) ->
							match gl with
							|head :: tail -> if (g1 = head) then false else g_notin_gl(g1, tail) 
							|[] -> true
						in
						match probe_gl_in with
						| h :: t -> if g_notin_gl(h, t) then h :: probe_giftlist(t) else probe_giftlist(t)
						| [] -> []
					in
					let ascending_Compare : gift -> gift -> int = fun gl1 gl2 ->
						if (gl1 > gl2) then 1 else (if (gl1 = gl2) then 0 else -1)
					in
					List.sort ascending_Compare (probe_giftlist(items_gl_in))
				in
				(* print_endline("cond_eval"); *)
				match condeval_cond_in with
				| Items (gl_cond) -> (*print_endline("Items");*)sort_items_giftlist (gl_cond)
				| Same (id_cond) -> (*print_endline("Same");*)search_id_from_giftlist(id_cond, condeval_idgift_list_in)
				| Common (cond_1, cond_2) -> (*print_endline("Common");*)sort_common_giftlist( cond_eval (cond_1, condeval_idgift_list_in), cond_eval(cond_2, condeval_idgift_list_in))
				| Except (cond_1, gl_cond) -> (*print_endline("Except");*)sort_subtract_giftlist(cond_eval(cond_1, condeval_idgift_list_in), gl_cond)
			in
			let rec condlist_eval : ((cond list) * ((id *  (gift list)) list)) -> gift list = fun (condlisteval_condlist_in, condlisteval_idgift_list_in) ->
				let sort_add_giftlist : ((gift list) * (gift list)) -> gift list = fun (gl1, gl2) ->
					let rec add_giftlist : ((gift list) * (gift list)) -> gift list = fun (add_gl1, add_gl2) ->
						let rec gift_notin_giftlist : gift * (gift list) -> bool = fun (gift_in, gl_in) ->
							(* print_endline("gift_notin_giftlist"); *)
							match gl_in with
							| head :: tail -> if ( head = gift_in) then false else gift_notin_giftlist (gift_in, tail)
							| [] -> true
						in
						(*print_endline("add_giftlist"); *)
						match add_gl2 with
						| h:: t -> (if (gift_notin_giftlist(h , add_gl1))  then h :: add_giftlist(add_gl1, t) else add_giftlist(add_gl1,t))
						| [] -> add_gl1
					in
					let ascending_Compare : gift -> gift -> int = fun gl1 gl2 ->
						if (gl1 > gl2) then 1 else (if (gl1 = gl2) then 0 else -1)
					in
					(* print_endline("sort_add_giftlist");*)
					(List.sort ascending_Compare (add_giftlist (gl1, gl2)))
				in
				(*print_endline("condlist_eval");*)
				match condlisteval_condlist_in with
				| h:: t -> sort_add_giftlist (cond_eval (h, condlisteval_idgift_list_in), condlist_eval (t, condlisteval_idgift_list_in))
				| [] -> []
			in
			(* print_endline("req_eval"); *)
			((fst reqeval_req_in), condlist_eval((snd reqeval_req_in), reqeval_idgift_list_in))
		in
		(
		(* printList iter_idgift_list_in ; *)
		(*print_endline("iter_once");*)
		match iter_req_list_in with
		| h:: t -> req_eval (h, iter_idgift_list_in) :: iteration_once (t, iter_idgift_list_in)
		| [] ->  []
		)
	in
	let rec iteration_converge : (require list * ((id *gift list) list) *((id *gift list) list)) -> ( (id * gift list) list) * ((id * gift list) list) = fun (iterconv_req_list_in, iterconv_idgift_list_cur, iterconv_idgift_list_prev) ->
		let rec idgift_list_equal : ((id * gift list) list) * ((id * gift list) list) -> bool = fun (idgift_list_1, idgift_list_2) ->
			let id_match : (id * id) -> bool = fun (id1, id2) ->
				match id1 with
				|A -> (match id2 with |A -> true |_ -> false)
				|B -> (match id2 with |B -> true |_ -> false)
				|C -> (match id2 with |C -> true |_ -> false)
				|D -> (match id2 with |D -> true |_ -> false)
				|E -> (match id2 with |E -> true |_ -> false)
			in
			let rec giftlist_match : ((gift list) * (gift list)) -> bool = fun (gl1, gl2) ->
				(* print_endline("giftlist_match");*)
				match gl1 with
				|g1h :: g1t ->
					(match gl2 with
					|g2h :: g2t -> if (g1h = g2h) then giftlist_match (g1t, g2t) else false
					|[] -> false)
				| [] -> (match gl2 with
					|g2h :: g2t -> false
					|[] -> true
					)
			in
			(*print_endline("idgift_list_equal");*)
			match idgift_list_1 with
			| (id_1, list_1_h) :: list_1_t ->
				(match idgift_list_2 with
				|(id_2, list_2_h) :: list_2_t ->(id_match (id_1,id_2))&&(giftlist_match(list_1_h,list_2_h))&&(idgift_list_equal(list_1_t,list_2_t))
				|[] -> false
				)
			| [] -> (match idgift_list_2 with
				| h:: t -> false
				| [] -> true 
				)
		in
		(* print_endline("iteratrion_converge");*)
		if (idgift_list_equal (iterconv_idgift_list_cur, iterconv_idgift_list_prev)) then (iterconv_idgift_list_cur, iterconv_idgift_list_cur)
		else iteration_converge (iterconv_req_list_in,iteration_once(iterconv_req_list_in, iterconv_idgift_list_cur) ,iterconv_idgift_list_cur)
	in
	(*print_endline("shoppingList");*)
	let (formatted_req_list_in) = formatting_req_list (req_list_in) in
	let (answer, _) = iteration_converge (formatted_req_list_in, (A,[])::(B,[])::(C,[])::(D,[])::(E,[])::[], (A,[])::(B,[])::(C,[])::(D,[])::(E,1::2::3::[])::[]) (* differentiationg initial prev and cur *)
	in  answer 
	;;

(*	
 
(*shoppingList([(A,[Common(Same(B),Same(C))]);(B,[Common(Same(A),Same(C))]);(C,[Common(Same(B),Same(A))])])*)

(*shoppingList ( [
      (A, [Items [1; 2]; Common (Same (B), Same (C))]);
      (B, [Common (Same (C), Items [2; 3])]);
      (C, [Items [1]; Except (Same (A), [3])])])
*)
shoppingList ( [
      (A, [Items [1; 2]; Common (Same (B), Same (C))]);
      (B, [Common (Same (C), Items [2; 3])]);
      (C, [Except(Same (A), [3])])
]);

print_endline(" ");
shoppingList [
      (A, [Items [1; 2; 3]; Except (Items [5; 6; 7], [6]); Common (Same (D), Same (E))]);
      (B, [Common (Same (A), Same (B)); Common (Same (B), Same (C)); Except (Same (D), [9])]);
      (C, [Common (Same (B), Same (C)); Except (Same (E), [1; 6]); Common (Same (A), Same (D))]);
      (D, [Items [4; 5; 6; 7; 8; 9; 10]; Same (B); Same (C)]);
      (E, [Except (Same (A), [3]); Items [9; 10; 11]; Common (Common (Same (B), Same (D)), Items [1; 2; 3; 4; 5; 6; 7])])]; 

print_endline(" ");
(shoppingList []);
print_endline(" ");
(shoppingList [ (A, []); (B, []); (C, []); (D, []); (E, []); ]); 
print_endline(" ");
(shoppingList [ (A, [Same B]); (B, [Same C]); (C, [Same D]); (D, [Same E]); (E, [Same A])] );
print_endline(" ");
(shoppingList [ 
(A, [Items [1;2;3]]); (B, [Items [2;3;4]]); 
(C, [Items [3;4;1]]); (D, [Items [4;1;2]]); 
(E, [Items [1;2;3;1;2;3]]); 
]); 
print_endline(" ");
(shoppingList [ 
(A, [Items [1;2;3]]); 
(B, [Same A]); 
(C, [Same A; Items[1;2]]); 
(D, [Same A; Items[4]]); 
(E, [Same D])]); 
print_endline(" ");
(shoppingList [ 
(A, [Common (Items [1;2;3], Items [2;1;3])]); 
(B, [Common (Items [2;1;3], Items [5;6;1;4;2;3])]); 
(C, [Common (Items [1;2;3], Items [4;5;6])]); 
(D, [Common (Items [3;2;1], Items [1])]); 
(E, [Common (Items [1;2;3], Items [])]); 
]); 
print_endline(" ");
(shoppingList [ 
(B, [Common (Items [2;1;3], Items [5;6;1;4;2;3])]); 
(E, [Common (Items [], Items [])]); 
(D, [Common (Items [1], Items [1])]); 
]);
print_endline(" ");
(shoppingList [ 
(A, [Except (Items [3;2;1], [3;2;1])]); 
(B, [Except (Items [2;1;3], [])]); 
(C, [Except (Items [2;1;3], [1;2;3;4;5;6])]); 
(D, [Except (Items [], [2;1;3])]); 
(E, [Except (Items [], [])])]); 
print_endline(" ");
(shoppingList [ 
(A, [Common (Common (Same B, Same C), Common (Same D, Same E))]); 
(B, [Common (Same C, Common (Same D, Except (Same E, [5])))]); 
(C, [Same D; Items[7;8]]); 
(D, [Except (Same E, [1;2;3])]); 
(E, [Items [1;2;3;4;5]])]);
print_endline(" "); 
(shoppingList [ 
(A, [Same B; Same C]); 
(B, [Except (Same C, [1;2;3]); Same D]); 
(C, [Items [1;2;3]; Items [3;4;5]; Common (Same A, Items [6;7])]); 
(D, [Same E]); 
(E, [Same D; Items[6;8]])]);
print_endline(" "); 
(shoppingList [ 
(A, [Common (Same B, Common (Except (Items [1;2;3;4;5], [1;3;5]), Same C)); Items [2;4;8]]); 
(B, [Except (Except (Except (Same A, [1]),[1;2]),[3]); Items [3;6;9]]); 
(C, [Same A; Same B; Same D; Same E]); 
(D, [Items [10]; Common (Same A, Same D); Items [5]]); 
(E, [Common (Same C, Common (Same A, Common (Same D, Same B)))])]);
print_endline(" "); 
(shoppingList [ 
(A, [Items [1;2;3;1;2;3]]); 
(D, [Items [5;5;5;5;5]]); 
(A, [Same D]); 
(E, [Except (Items [1;2;3;1;2;3], [1;2;3])]); 
(A, [Items [1;2;3;4]])]); 
(* 
]) = [(A, []); (B, [1; 2; 3]); (C, []); (D, []); (E, [])]); 
]) = [(A, [4]); (B, [4]); (C, [4; 5; 7; 8]); (D, [4; 5]); (E, [1; 2; 3; 4; 5])]); 
]) = [(A, [1; 2; 3; 4; 5; 6; 8]); (B, [4; 5; 6; 8]); (C, [1; 2; 3; 4; 5; 6]); (D, [6; 8]); (E, [6; 8])]); 
]) = [(A, [2; 4; 8]); (B, [3; 4; 6; 8; 9]); (C, [2; 3; 4; 5; 6; 8; 9; 10]); (D, [5; 10]); (E, [])]); 
]) = [(A, [1; 2; 3; 4; 5]); (B, []); (C, []); (D, [5]); (E, [])]); 

(*
print_endline "1"; 

print_endline "2"; 

print_endline "3"; 

]) = [(A, [1; 2; 3]); (B, [1; 2; 3]); (C, [1; 2; 3]); (D, [1; 2; 3; 4]); (E, [1; 2; 3; 4])]); 
print_endline "4"; 

print_endline "5"; 

print_endline "6"; 

print_endline "7"; 

print_endline "8"; 

print_endline "9"; 

print_endline "10"; 

*)
print_endline("pass all tests")
*)
*)
