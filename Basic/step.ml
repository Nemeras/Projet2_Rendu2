			(** ETAPES DE L'ALGORITHME **)

(* On donne ici les implémentations des fonctions utilisées dans l'algorithme, dans dpll.ml *)


open Array

open Stack
open Print_step
open Learning

open DynArray
open Arbre
		(** BOOLEAN CONSTRAINT PROPAGATION **)


(* Cherche  un littéral présent dans une clause unitaire non encore vraie.
   Renvoie 0 s'il y a une contradiction, ou si un tel littéral n'existe pas. *)
let find_unit current solution =
	if solution.(0) = 0 then
		let i = ref 0 in
		let lit = ref 0 in
		let found = ref false in
		while not !found && !i < current.length do
			let b, c, _ = current.a.(!i) in
			if not b && List.tl c = [] then
				begin
				found := true ;
				lit := List.hd c
				end
			else
				incr i
		done ;
		if !found then 
			!lit, !i
		else
			0,0
	else
		0,0


(** A RAJOUTER AU DEBUT DE L'EXECUTION **)
(* Cherche un littéral dont la valeur est inconnue mais dont la négation n'apparaît pas dans current.
   Renvoie 0 si un tel littéral n'existe pas.                                                         *)
(*let find_single pos solution =
	let found = ref false in
	let i = ref 1 in
	while not !found && !i < length pos do
		if solution.(!i) = 0 && fst pos.(!i) = [] && snd pos.(!i) <> [] then
			(* La variable i n'est présente que négativement *)
			begin
			i := - !i ;
			found := true
			end
		else if solution.(!i) = 0 && snd pos.(!i) = [] && fst pos.(!i) <> [] then
			(* La variable i n'est présente que positivement *)
			found := true
		else
			incr i
	done ;
	if !found then
		!i
	else
		0
*)

(* Cherche un littéral conséquence de current, i.e. présent dans une clause unitaire ou dont l'opposé
   n'apparait pas dans current.
   Renvoie 0 si un tel littéral n'existe pas.                                                         *)
let find_consequences current pos solution =
	(*let tmp = find_single pos solution in
	if tmp <> 0 then
		tmp
	else*)
		find_unit current solution


(* Effectue la boolean constraint propagation sur toutes les variables présentes sous une seule polarité
   ou présentes dans une clause unitaire.                                                                *)
let rec propa stack current pos solution levels orders level print =
	let a, b = find_consequences current pos solution in
	let x = ref a in
	let y = ref b in
	let compt = ref 1 in
	for i = 1 to Array.length solution - 1 do
		if solution.(i) != 0 && levels.(i) = level && orders.(i)+1 > !compt then
			compt := orders.(i) + 1 ;
	done ;
	while !x <> 0 do
		if solution.(0) < 0 then
			x := 0
		else
			begin
			print_conseq !x print ;
			if levels.(abs !x) != -1 then
				levels.(abs !x) <- level ;
			if !x > 0 then
				(* x est nécessairement à vrai *)
				begin
				solution.(!x) <- !y + 2 ;
				update !x stack current pos solution levels (snd pos.(!x)) (fst pos.(!x)) level
				end
			else
				(* x est nécessairement à faux *)
				begin
				solution.(- !x) <- - !y - 2 ;
				update !x stack current pos solution levels (fst pos.(- !x)) (snd pos.(- !x)) level
				end
			;
			orders.(abs !x) <- !compt ;
			incr compt ;
			let a, b = find_consequences current pos solution in
			x := a ;
			y := b ;
			end
	done




		(** PARIS ET BACKTRACKING **)


(* Effectue une étape de backtrack *)
let backtrack_step stack current pos solution levels orders k back nb_back level nb_back print =
	
	(* Si la valeur de début de pile est positive et n'est pas issue d'une boolean constraint propagation,
	   donc pas nécessaire, on peut supposer l'opposé. On arrête alors le backtrack.                       *)
	if nb_back = 0 && !k > 0 && solution.(!k) = 1 then
		begin
		solution.(0) <- 0 ;
		back := false ;
		k := backtrack stack current pos (snd pos.(!k)) !level ;	(* On retire !k *)
		solution.(!k) <- 0 ;
		decr level ;
		print_backtrack !k solution.(abs !k) print ;
		propa stack current pos solution levels orders !level print ;
		if solution.(!k) = 0 && solution.(0) = 0 then
			begin
			k := - !k ;
			incr level ;
			levels.(- !k) <- !level ;
			update !k stack current pos solution levels (fst pos.(- !k)) (snd pos.(- !k)) !level ;	(* On suppose l'opposé *)
			print_hyp !k print ;
			solution.(- !k) <- -1 ;
			orders.(- !k) <- 0
			end
		end
	
	(* Sinon, il faut continuer le backtrack *)
	else
		begin
		if !k > 0 then
			k := backtrack stack current pos (snd pos.(!k)) !level
		else
			k := backtrack stack current pos (fst pos.(- !k)) !level
		;
		if abs solution.(abs !k) = 1 then
			decr level ;
		print_backtrack !k solution.(abs !k) print ;
		solution.(abs !k) <- 0 ;
		k := pick stack
		end



let rec hlev clause solution levels ign =
	match clause with
	| []-> -1
	| h::t when (*abs (solution.(abs h)) = 1 &&*) (abs h) <> (abs ign) -> max (levels.(abs h)) (hlev t solution levels ign)
	| h::t -> hlev t solution levels ign


(* Implémente une itération de la boucle *)
let continue bonus stack clauses current pos solution levels orders k back nb_back level print draw tableau_bonus=
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
		
		let g = graph current solution !level !activate in
		let new_clause, blue = iter_learning bonus g clauses current solution levels orders (-solution.(0)-1) !level !activate tableau_bonus in
		if !activate then
			Dot.compile g (Array.length solution - 1)
		;
		
		k := pick stack ;		(* On a besoin de connaître la valeur à dépiler *)
		print_new_backtrack print ;
		back := true ;
		let clause_mod = Stack.maj_clause_learning stack new_clause pos levels (clauses.length) in 
		DynArray.add clauses new_clause [] ;
		DynArray.add current clause_mod (false,[],[]) ;
		print_string (Cnf.string_of_clause new_clause) ;
		(*Printf.printf "%d %d %d\n" solution.(2) solution.(10) solution.(15) ;*)
		let x = hlev new_clause solution levels blue in
		(*print_int x ; print_newline() ;*)
		(*print_int blue ; print_newline() ;*)
		if x = -1 then
			begin
			levels.(abs blue) <- -1 ;
			nb_back:= 1
			end
		else
			nb_back:= !level + 1  - x ;
		(*print_int !nb_back;
		print_newline();*)
		end
	
	(* Backtracking : on n'a pas encore pu faire de nouvelle hypothèse pour enlever la contradiction *)
	else if !back then
		begin
		(*print_int !nb_back ; print_newline() ;*)
		(*if !nb_back > 0 then
			while !nb_back > 0 do*)
				if abs solution.(abs !k) = 1 && !nb_back > 0 then
					decr nb_back ;
				backtrack_step stack current pos solution levels orders k back !nb_back level !nb_back print
			(*done
		else
			backtrack_step stack current pos solution levels orders k back level 0 print*)
		end
	
	(* S'il n'y a pas de contradiction : on suppose par défaut la première variable libre comme vraie *)
	else
		begin
		k := abs !k + 1 ;
		if solution.(!k) = 0 then
			begin
			incr level ;
			levels.(!k) <- !level ;
			print_hyp !k print ;
			update !k stack current pos solution levels (snd pos.(!k)) (fst pos.(!k)) !level ;
			solution.(!k) <- 1 ;
			orders.(!k) <- 0
			end
		end
