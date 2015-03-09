			(** ALGORITHME DPLL **)

(* La structure principale de l'algorithme DPLL ; la pile est gérée dans stack.ml, les étapes intermédiaires dans step.ml *)


open List
open Array

open Cnf
open Step
open Stack
open Print_step




		(** STRUCTURE DE DONNEE - VARIABLES **)


(*type changing_clauses = (bool*clause*(int*int list)) array*)


(* On manipule les clauses dans le tableau current.
   fst current.(i) indique si la clause est actuellement satisfaite, et snd current.(i)
   est la clause d'indice i courante, qui peut être modifiée pendant l'exécution de l'algorithme. *)

(* Variables utilisées dans la suite, et dans step.ml :
	stack : la pile des affectations.
	k : référence du littéral considéré à chaque étape.
	back : référence de booléen valant vrai si l'algorithme est en phase de backtracking,
		vrai sinon.
	print : vrai si l'affichage est activé, faux sinon.
   Les fonctions update et backtrack sont explicitées dans stack.ml.                              *)

(* solution désigne dans la suite l'instanciation courante des variables :
	solution.(k) = 1 si la variable k est à vrai suite à un pari / une hypothèse.
	             > 1 si la variable k est à vrai suite à une propagation / déduction.
	solution.(k) = -1 si la variable k est à faux suite à un pari / une hypothèse.
	             < -1 si la variable k est à faux suite à une propagation / déduction.
	solution.(k) = 0 si la valeur de la variable k est indéterminée                           *)





		(** INITIALISATION **)


(* Renvoie le tableau current correspondant à la CNF cnf.
   Renvoie également un tableau pos : pos.(i) = l1, l2, où l1 est la liste des indices
   des clauses contenant le littéral i, et l2 la liste de celles contenant le littéral -i *)
let cnf_to_vect cnf solution =
	let clauses = make (List.length cnf.clauses) [] in
	let current = make (List.length cnf.clauses) (false,[],[]) in
	let pos = make (cnf.v_real+1) ([],[]) in
	
	(* Enumère chaque clause et met à jour current et pos *)
	let rec aux clauses_list i =
		match clauses_list with
		| [] -> ()
		| []::_ ->
			solution.(0) <- -2		(* Clause vide rencontrée : cnf n'est pas satisfiable *)
		| c::tail ->
			activate_clause c pos i ;	(* Mise à jour de pos *)
			clauses.(i) <- c ;
			current.(i) <- false, c, [] ;
			aux tail (i+1)
	in
	aux cnf.clauses 0 ;
	clauses, current, pos


(* Détermine la première hypothèse à faire, après avoir éliminé les clauses unitaires
   et les variables présentes sous une seule polarité.                                *)
let init cnf stack current pos solution levels print =
	
	(* On déduit les conséquences possibles *)
	propa stack current pos solution levels (-1) print ;
	
	let k = ref 1 in
	(* Si, après les affectations nécessaires, on n'a pas trouvé de contradiction, on peut continuer *)
	if solution.(0) = 0 then
		begin
		while !k <= cnf.v_real && solution.(!k) <> 0 do
			incr k
		done ;
		(* k : première variable non instanciée *)
		if !k <= cnf.v_real then
			begin
			solution.(!k) <- 1 ;
			update !k stack current pos solution (snd pos.(!k)) (fst pos.(!k)) 0
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

let solve cnf print =
	
	(* Tri des littéraux dans les clauses par indice de variable croissant,
	   élimination des tautologies.                                         *)
	ordo cnf ;
	
	(* Initialisation de current, pos, solution et de la pile des instanciations *)
	let solution = make (cnf.v_real+1) 0 in
	let levels = make (cnf.v_real+1) 0 in
	let clauses, current, pos = cnf_to_vect cnf solution in
	let stack = create_stack () in		(* stack contient initialement 0 en fond de pile *)
	
	(* Détection des clauses unitaires et des variables sous une seule polarité *)
	let k = init cnf stack current pos solution levels print in
	
	
	(* Boucle principale *)
	let back = ref false in
	let compt = ref 0 in
	let level = ref 0 in
	while abs !k <= cnf.v_real && !k <> 0 do
		incr compt ;
		
		(* Affichage, si autorisé *)
		if print then
			print_step current solution !back !compt ;
		
		(* Détection des clauses unitaires et des variables sous une seule polarité *) 
		if solution.(0) = 0 then
			propa stack current pos solution levels !level print ;
		
		(* Si toutes les variables ont été instanciées *)
		if abs !k = cnf.v_real then
			(* S'il y a contradiction : backtrack *)
			if solution.(0) < 0 then
				continue stack clauses current pos solution levels k back level print
			(* Sinon : c'est fini *)
			else
				k := cnf.v_real + 1
		(* Sinon : on continue *)
		else
			continue stack clauses current pos solution levels k back level print
	done ;
	
	
	if !k = 0 then
		False
	else
		True solution
