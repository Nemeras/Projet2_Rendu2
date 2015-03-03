			(** GESTION DE LA PILE **)

(* Remarque : les opérations sur les clauses sont gérées dans watched.ml *)


open List

open Watched


		(** STRUCTURE DE PILE **)

(* Chaque étage de la pile contient un entier indiquant le pari / la déduction effectuée
   (le littéral qui a été mis à vrai). La fin de la pile est toujours 0.                 *)

type stack = int list ref

let create_stack () =
	ref [0]

let is_empty liste =
	match !liste with
	| [] -> true
	| _ -> false

(* Renvoie l'élément de tête de la liste. *)
let pick stack =
	hd !stack




		(** UPDATE / PUSH **)


(* Place l'affectation n = vrai au début de la pile, renvoie la liste des conséquences (clauses unitaires) apparues. *)
let update n stack current solution =
	let consequences = ref [] in
	stack := n::!stack ;
	
	for i = 0 to Array.length current - 1 do
		(* Si un des deux littéraux de la clause n'est pas encore à vrai *)
		if not (is_w_true current.(i) solution) then
			begin
			
			(* On modifie les littéraux surveillés suite à l'affectation en cours *)
			current.(i) <- change_clause current.(i) solution ;
			
			(* Détection d'une conséquence *)
			if is_unit current.(i) solution then
				consequences := (hd current.(i))::!consequences ;
			
			(* Si la clause est à faux, il y a contradiction *)
			is_clause_false current.(i) solution ;
			end
		
		(* Sinon, on ignore cette clause *)
	done ;
	
	!consequences




		(** BACKTRACK / POP **)


(* Annule l'affectation en tête de liste et la renvoie. *)
let backtrack stack =
	let n = hd !stack in
	stack := tl !stack ;
	n



