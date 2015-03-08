			(** GESTION DE LA PILE **)



open List


		(** STRUCTURE DE PILE **)

(* Chaque étage de la pile contient :
	* Un entier indiquant le pari / la déduction effectuée (le littéral qui a été mis à vrai).
	* Une liste d'entiers indiquant quelles clauses sont mises à vrai lorsque ce littéral l'est.
   La fin de la pile est toujours 0,[].                                                              *)

type stack = (int*int*(int*int list)) list ref

let create_stack () =
	ref [(0,0,[])]

let is_empty stack =
	match !stack with
	| [] -> true
	| _ -> false

(* Renvoie l'élément de tête de la liste. *)
let pick stack =
	let k, _, _ = hd !stack in
	k

let hlevel stack =
	let _, l, _ = hd !stack in
	l



		(** ACTIVATION / DESACTIVATION DE CLAUSES **)


(* Réactualise pos lorsque c est activée = indéterminée. *)
let activate_clause c pos i =
	let rec aux c =
		match c with
		| [] -> ()
		| x::q when x > 0 ->
			pos.(x) <- i::(fst pos.(x)), snd pos.(x) ;
			aux q
		| x::q ->
			pos.(-x) <- fst pos.(-x), i::(snd pos.(-x)) ;
			aux q
	in
	aux c


(* Réactualise pos lorsque c est désactivée = vraie. *)
let inactivate_clause c pos i =
	let rec aux c =
		match c with
		| [] -> ()
		| x::q when x > 0 ->
			pos.(x) <- filter (fun y -> y <> i) (fst pos.(x)), snd pos.(x) ;
			aux q
		| x::q ->
			pos.(-x) <- fst pos.(-x), filter (fun y -> y <> i) (snd pos.(-x)) ;
			aux q
	in
	aux c




		(** UPDATE / PUSH **)


(* Supprime les littéraux mis à faux par l'affectation encours dans les clauses correspondantes. *)
let rec update_remove n stack current solution list_pos level =
	match list_pos with
	| [] -> ()
	| h::t ->
		let boole, c, c2 = current.(h) in
		let new_c = List.filter (fun i -> i <> n) c in
		current.(h) <- boole, new_c, (n,level)::c2 ;
		if new_c = [] then
			solution.(0) <- -h-1 ;
		update_remove n stack current solution t level


(* Désactive les clauses mises à vrai par l'affectation en cours. *)
let rec update_inactivate n stack current pos list_pos =
	match list_pos with
	| [] -> [] ;
	| h::t ->
		let boole, c, c2 = current.(h) in
		if not boole then
			begin
			current.(h) <- true, c, c2 ;
			inactivate_clause c pos h
			end
		;
		h::(update_inactivate n stack current pos t)


(* Place l'affectation n = vrai au début de la pile, et met à jour current et pos.
	list_pos_negative : liste des positions dans current des clauses contenant le littéral -n.
	list_pos : liste des positions dans current des clauses contenant le littéral n.           *)
let update n stack current pos solution list_pos_negative list_pos level =
	let changes = update_inactivate n stack current pos list_pos in
	update_remove (-n) stack current solution list_pos_negative level ;
	stack := (n,level,changes)::!stack




		(** BACKTRACK / POP **)


(* Réactive les clauses qui avaient été désactivées par l'affectation annulée. *)
let rec backtrack_activate n changes current pos =
	match changes with
	| [] -> ()
	| h::t ->
		let _, c, c2 = current.(h) in
		current.(h) <- false, c, c2 ;
		activate_clause c pos h ;
		backtrack_activate n t current pos


let rec aux_restore c2 level =
	match c2 with
	| [] -> []
	| (_,l)::_ when l < level -> c2
	| (n,l)::q ->
		aux_restore q level

(* Restaure les littéraux qui avaient été supprimés par l'affectation annulée. *)
let rec backtrack_restore n to_restore current level =
	match to_restore with
	| [] -> ()
	| h::tail ->
		let boole, c, c2 = current.(h) in
		let new_c2 = aux_restore c2 level in
		current.(h) <- boole, n::c, new_c2 ;
		backtrack_restore n tail current level


(* Annule l'affectation en tête de liste, la renvoie, et met à jour current et pos. *)
let backtrack stack current pos to_restore level =
	let content = !stack in
	match content with
	| [] -> failwith "Pile vide"
	| (n, _, changes)::tail ->
		backtrack_activate n changes current pos ;
		stack := tail ;
		backtrack_restore (-n) to_restore current level ;
		n
