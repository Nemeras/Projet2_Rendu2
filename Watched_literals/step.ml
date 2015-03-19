			(** ETAPES DE L'ALGORITHME **)

(* On donne ici les implémentations des fonctions utilisées dans l'algorithme, dans dpll.ml *)


open Stack
open Print_step
open Learning




		(** BOOLEAN CONSTRAINT PROPAGATION **)


(* Trouve toutes les conséquences des clauses unitaires (units) apparues à cette étape *)
let rec propa units stack current solution levels orders level print =
	let rec aux units num =
		match units with
		| [] -> ()
		| _ when solution.(0) < 0 -> ()
		| (x,i)::tail when solution.(abs x)*x >= 0 ->
			if x > 0 then
				solution.(x) <- i + 2
			else
				solution.(-x) <- -i - 2
			;
			levels.(abs x) <- level ;
			orders.(abs x) <- num ;
			print_conseq x print ;
			let l = update x stack current solution in
			aux (l@tail) (num+1)
		| (_,i)::_ ->
			()(*solution.(0) <- -1-i*)
	in
	aux units 1




		(** PARIS ET BACKTRACKING **)


(* Effectue une étape de backtrack *)
let backtrack_step stack current solution levels orders uni k back level print =
	
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
		levels.(- !k) <- !level ;
		solution.(- !k) <- -1 ;
		orders.(- !k) <- 0 ;
		end
	
	(* Sinon, il faut continuer le backtrack *)
	else
		begin
		if abs solution.(abs !k) = 1 then	
			decr level ;
		print_backtrack !k solution.(abs !k) print ;
		solution.(abs !k) <- 0 ;
		k := backtrack stack ;
		k := pick stack
		end



(* Implémente une itération de la boucle *)
let continue stack clauses current solution levels orders uni k back level print draw =
	
	(* On vient de découvrir la clause vide : on commence le backtrack *)
	if solution.(0) < 0 && not !back then
		begin
		let activate = ref false in
		if !draw then
			begin
				print_string "\nConflit détecté. Que voulez-vous faire ?\ng : générer le graphe des confits\nc : continuer jusqu'au prochain conflit\nt : désactiver le mode interactif\n\n" ;
				flush stdout ;
				let key = Scanf.scanf "%c\n" (fun x -> x) in
				match key with
				| 'g' -> activate := true
				| 't' -> draw := false
				| 'c' -> ()
				| _ -> failwith "Saisie erronée\n"
			end
		;
		
		let g = graph current solution levels orders !level !activate in
		let new_clause = iter_learning g clauses current solution levels orders (-solution.(0)-1) !level !activate in
		print_string (Cnf.string_of_clause new_clause) ;
		if !activate then
			Dot.compile g (Array.length solution - 1)
		;
		
		k := pick stack ;		(* On a besoin de connaître la valeur à dépiler *)
		print_new_backtrack print ;
		back := true
		end
	
	(* Backtracking : on n'a pas encore pu faire de nouvelle hypothèse pour enlever la contradiction *)
	else if !back then
		backtrack_step stack current solution levels orders uni k back level print
	
	(* S'il n'y a pas de contradiction : on suppose par défaut la première variable libre comme vraie *)
	else
		begin
		k := abs !k + 1 ;
		if abs solution.(!k) < 1 then
			begin
			incr level ;
			print_hyp !k print ;
			solution.(!k) <- 1 ;
			levels.(!k) <- !level ;
			orders.(!k) <- 0 ;
			uni := update !k stack current solution ;
			end
		end
