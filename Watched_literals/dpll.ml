			(** ALGORITHME DPLL **)

(* La structure principale de l'algorithme DPLL ; la pile est gérée dans stack.ml, les étapes intermédiaires dans step.ml *)


open List
open Array

open Cnf
open Step
open Stack
open Watched
open Print_step



		(** STRUCTURE DE DONNEE - VARIABLES **)

(* On liste ici uniquement les changements par rapport à la version sans littéraux surveillés :
	* pos n'est plus utilisée.
	* current n'est plus qu'un tableau de clause : ce seront les littéraux surveillés qui
	  indiqueront si la clause est activée ou pas.
	* uni : clauses unitaires rencontrées dans la gestion de la pile.                       *)





		(** INITIALISATION **)


(* Renvoie la liste de clauses "clauses" dans laquelle on a supprimé toutes les clauses unitaires,
   et la clause vide le cas échéant. On ne les empile pas par commmodité.                          *)
let rec remove_units clauses solution levels print =
	match clauses with
	| [] -> []
	| [x]::tail when x*solution.(abs x) >= 0 ->
		solution.(abs x) <- 2*x ;
		levels.(abs x) <- -1 ;
		print_conseq x print ;
		remove_units tail solution levels print
	| [x]::tail ->
		solution.(0) <- -2 ;
		[]
	| []::tail ->
		solution.(0) <- -2 ;
		[]
	| c::tail -> c::(remove_units tail solution levels print)


(* Renvoie le tableau current correspondant à la liste de clauses "clauses". *)
let cnf_to_vect cl =
	let clauses = make (List.length cl) [] in
	let current = make (List.length cl) [] in
	let rec aux cl i =
		match cl with
		| [] -> ()
		| c::tail ->
			current.(i) <- c ;
			clauses.(i) <- c ;
			aux tail (i+1)
	in
	aux cl 0 ;
	clauses, current


(* Détermine la première hypothèse à faire, après avoir éliminé les clauses unitaires
   et les variables présentes sous une seule polarité.                                *)
let init cnf stack current solution levels orders uni print =
	
	(* Remise en forme des clauses avec littéraux surveillés après les premières affectations,
	   qui n'on pas été empilées.                                                              *)
	for i = 0 to length current - 1 do
		current.(i) <- all_false_to_end current.(i) solution ;
		if is_unit current.(i) solution then
			uni := (hd current.(i), i)::!uni 
	done ;
	
	(* On déduit les conséquences possibles *)
	propa !uni stack current solution levels orders (-1) print ;
	
	let k = ref 1 in
	(* Si, après les affectations nécessaires, on n'a pas trouvé de contradiction, on peut continuer *)
	if solution.(0) = 0 then
		begin
		while !k <= cnf.v_real && solution.(!k) <> 0 do
			incr k
		done ;
		if !k <= cnf.v_real then
			begin
			solution.(!k) <- 1 ;
			Print_step.print_hyp !k print ;
			uni := update !k stack current solution
			end
		end
	(* Sinon, on donne la valeur d'arrêt pour k *)
	else
		k := 0
	;
	k




		(** RESOLUTION - STRUCTURE DE DPLL **)



(* Renvoie une solution associée à la CNF cnf donnée en entrée :
	False si cnf n'est pas satisfiable.
	True solution si cnf est satisfiable, avec solution une instanciation qui la satisfait. *)

let solve cnf print draw =
	
	(* Tri des littéraux dans les clauses par indice de variable croissant,
	   élimination des tautologies.                                         *)
	ordo cnf ;
	
	(* Initialisation de current, solution et de la pile des instanciations.
           Elimination des clauses avec moins de un littéral.                    *)
	let solution = make (cnf.v_real+1) 0 in
	let levels = Array.make (cnf.v_real+1) 0 in
	let orders = Array.make (cnf.v_real+1) 0 in
	let cl = remove_units cnf.clauses solution levels print in
	let clauses, current = cnf_to_vect cl in
	let stack = create_stack () in
	
	(* Déductions découlant de remove_units, détermination du premier pari *)
	let uni = ref [] in
	let k = init cnf stack current solution levels orders uni print in
	
	
	(* Boucle principale *)
	let back = ref false in
	let compt = ref 0 in
	let level = ref 0 in
	while abs !k <= cnf.v_real && !k <> 0 do
		incr compt ;
		
		(* Boolean constraint propagation *)
		propa !uni stack current solution levels orders !level print ;
		uni := [] ;
		
		(* Affichage, si autorisé *)
		if print then
			print_step current solution !back !compt ;
		
		(* Si toutes les variables ont été instanciées *)
		if abs !k = cnf.v_real then
			(* S'il y a contradiction : backtrack *)
			if solution.(0) < 0 then
				continue stack clauses current solution levels orders uni k back level print draw
			(* Sinon : c'est fini *)
			else
				k := cnf.v_real + 1
		(* Sinon : on continue *)
		else
			continue stack clauses current solution levels orders uni k back level print draw
	done ;
	
	
	if !k = 0 then
		False
	else
		True solution
