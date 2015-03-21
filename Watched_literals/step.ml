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
		| (x,i)::tail when solution.(abs x) = 0 ->
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
		| (x,i)::tail -> aux tail num
	in
	let compt = ref 1 in
	for i = 1 to Array.length solution - 1 do
		if solution.(i) != 0 && levels.(i) = level && orders.(i)+1 > !compt then
			compt := orders.(i) + 1 ;
	done ;
	aux units !compt




		(** PARIS ET BACKTRACKING **)



let from_scratch stack current solution k level =
	if (!k != 0) then
		begin
		while !k != 0 do
			k := backtrack stack ;
			if abs solution.(abs !k) = 1 then
				decr level ;
			solution.(abs !k) <- 0 ;
			k := pick stack
		done ;
		k := 1 ;
		solution.(0) <- 1
		end


(* Effectue une étape de backtrack *)
let backtrack_step stack current solution levels orders uni k back nb_back level print =
	
	(* Si la valeur de début de pile est positive et n'est pas issue d'une boolean constraint propagation,
	   donc pas nécessaire, on peut supposer l'opposé. On arrête alors le backtrack.                       *)
	if nb_back = 0 && !k > 0 && solution.(!k) = 1 then
		begin
		solution.(0) <- 0 ;
		back := false ;
		k := backtrack stack ;
		print_backtrack !k solution.(abs !k) print ;
		solution.(!k) <- 0 ;
		levels.(!k) <- 0 ;
		decr level
		(*k := - !k ;
		solution.(- !k) <- -1 ;
		uni := update !k stack current solution ;
		print_hyp !k print ;
		levels.(- !k) <- !level ;
		orders.(- !k) <- 0 *)
		end
	
	(* Sinon, il faut continuer le backtrack *)
	else
		begin
		if abs solution.(abs !k) = 1 then	
			decr level ;
		print_backtrack !k solution.(abs !k) print ;
		solution.(abs !k) <- 0 ;
		levels.(abs !k) <- 0 ;
		k := backtrack stack ;
		k := pick stack
		end


let rec hlev clause solution levels ign =
	match clause with
	| []-> -1
	| h::t when (*abs (solution.(abs h)) = 1 &&*) (abs h) <> (abs ign) -> max (levels.(abs h)) (hlev t solution levels ign)
	| h::t -> hlev t solution levels ign


(* Implémente une itération de la boucle *)
let continue bonus stack clauses current solution levels orders uni k back nb_back level print draw tableau_bonus =
	
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
		let new_clause, blue = iter_learning bonus g clauses current solution levels orders (-solution.(0)-1) !level !activate tableau_bonus in
		print_string (Cnf.string_of_clause new_clause) ;
		if !activate then
			Dot.compile g (Array.length solution - 1)
		;
		
		if !k != 0 then
			k := pick stack ;		(* On a besoin de connaître la valeur à dépiler *)
		print_new_backtrack print ;
		back := true ;
		
		let clause_mod = Stack.maj_clause_learning stack new_clause levels (clauses.length) in
		DynArray.add clauses new_clause [] ;
		DynArray.add current clause_mod [] ;
		
		let x = hlev new_clause solution levels blue in
		if x = -1 then
			from_scratch stack current solution k level
		else
			nb_back:= !level + 1 - x
		end
	
	(* Backtracking : on n'a pas encore pu faire de nouvelle hypothèse pour enlever la contradiction *)
	else if !back then
		begin
		if abs solution.(abs !k) = 1 && !nb_back > 0 then
			decr nb_back ;
		backtrack_step stack current solution levels orders uni k back !nb_back level print
		end
	
	(* S'il n'y a pas de contradiction : on suppose par défaut la première variable libre comme vraie *)
	else
		begin
		if !k > 0 && solution.(!k) = 0 then
			begin
			incr level ;
			print_hyp !k print ;
			solution.(!k) <- 1 ;
			levels.(!k) <- !level ;
			orders.(!k) <- 0 ;
			uni := update !k stack current solution ;
			end ;
		k := abs !k + 1 ;
		end
