			(** ETAPES DE L'ALGORITHME **)

(* On donne ici les implémentations des fonctions utilisées dans l'algorithme, dans dpll.ml *)


open Stack
open Print_step




		(** BOOLEAN CONSTRAINT PROPAGATION **)


(* Trouve toutes les conséquences des clauses unitaires (units) apparues à cette étape *)
let rec propa units stack current solution print =
	match units with
	| [] -> ()
	| _ when solution.(0) < 0 -> ()
	| x::tail when solution.(abs x)*x >= 0 ->
		solution.(abs x) <- 2*x ;
		print_conseq x print ;
		let l = update x stack current solution in
		propa (l@tail) stack current solution print
	| _ ->
		solution.(0) <- -2




		(** PARIS ET BACKTRACKING **)


(* Effectue une étape de backtrack *)
let backtrack_step stack current solution uni k back print =
	
	(* Si la valeur de début de pile est positive et n'est pas issue d'une boolean constraint propagation,
	   donc pas nécessaire, on peut supposer l'opposé. On arrête alors le backtrack.                       *)
	if !k > 0 && solution.(!k) = 1 then
		begin
		solution.(0) <- 0 ;
		back := false ;
		k := backtrack stack ;
		print_backtrack !k solution.(abs !k) print ;
		k := - !k ;
		solution.(- !k) <- -1 ;
		uni := update !k stack current solution ;
		print_hyp !k print ;
		end
	
	(* Sinon, il faut continuer le backtrack *)
	else
		begin
		solution.(abs !k) <- 0 ;
		k := backtrack stack ;
		print_backtrack !k solution.(abs !k) print ;
		k := pick stack
		end


(* Implémente une itération de la boucle *)
let continue stack current solution uni k back print =
	
	(* On vient de découvrir la clause vide : on commence le backtrack *)
	if solution.(0) < 0 && not !back then
		begin
		k := pick stack ;		(* On a besoin de connaître la valeur à dépiler *)
		print_new_backtrack print ;
		back := true
		end
	
	(* Backtracking : on n'a pas encore pu faire de nouvelle hypothèse pour enlever la contradiction *)
	else if !back then
		backtrack_step stack current solution uni k back print
	
	(* S'il n'y a pas de contradiction : on suppose par défaut la première variable libre comme vraie *)
	else
		begin
		k := abs !k + 1 ;
		if abs solution.(!k) <= 1 then
			begin
			print_hyp !k print ;
			solution.(!k) <- 1 ;
			uni := update !k stack current solution ;
			end
		end
