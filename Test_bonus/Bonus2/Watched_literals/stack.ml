			(** GESTION DE LA PILE **)

(* Remarque : les opérations sur les clauses sont gérées dans watched.ml *)


open List

open Watched
open DynArray


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





(** A REFAIRE **)
let rec separate clause stack_e solution nb=
	match stack_e with
	| [] -> ()
	| v::tail ->
		solution.(abs v) <- v ;
		clause := change_clause !clause solution ;
		separate clause tail solution nb


let maj_clause_learning stack clause levels nb=
	let stack_e = List.rev !stack in
	let clause_r = ref clause in
	let solution = Array.make (Array.length levels) 0 in
	separate clause_r stack_e solution nb;
	!clause_r



		(** UPDATE / PUSH **)


(* Place l'affectation n = vrai au début de la pile, renvoie la liste des conséquences (clauses unitaires) apparues. *)
let update n stack current solution =
	let consequences = ref [] in
	stack := n::!stack ;
	let absurd = ref false in
	let i = ref 0 in
	while (!i < current.length && not !absurd)  do
		(* Si un des deux littéraux de la clause n'est pas encore à vrai *)
		if not (is_w_true current.a.(!i) solution) then
			begin
			
			(* On modifie les littéraux surveillés suite à l'affectation en cours *)
			current.a.(!i) <- change_clause current.a.(!i) solution ;
			
			(* Détection d'une conséquence *)
			if is_unit current.a.(!i) solution then
				consequences := (hd current.a.(!i), !i)::!consequences ;
			
			(* Si la clause est à faux, il y a contradiction *)
			is_clause_false current.a.(!i) solution ;
			if solution.(0) < 0 then
				begin
				solution.(0) <- -1 - !i ;
				absurd := true
				end
			end
		;
		
		(* Sinon, on ignore cette clause *)
		
		incr i
		
	done ;
	
	!consequences




		(** BACKTRACK / POP **)


(* Annule l'affectation en tête de liste et la renvoie. *)
let backtrack stack =
	let n = hd !stack in
	stack := tl !stack ;
	n



