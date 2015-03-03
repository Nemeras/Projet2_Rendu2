			(** ETAPES DE L'ALGORITHME **)

(* On donne ici les implémentations des fonctions utilisées dans l'algorithme, dans dpll.ml *)


open Array

open Stack
open Print_step




		(** BOOLEAN CONSTRAINT PROPAGATION **)


(* Cherche un littéral présent dans une clause unitaire non encore vraie.
   Renvoie 0 s'il y a une contradiction, ou si un tel littéral n'existe pas. *)
let find_unit current solution =
	if solution.(0) = 0 then
		let i = ref 0 in
		let found = ref false in
		while not !found && !i < length current do
			if not (fst current.(!i)) && List.tl (snd current.(!i)) = [] then
				begin
				found := true ;
				i := List.hd (snd current.(!i))
				end
			else
				incr i
		done ;
		if !found then 
			!i
		else
			0
	else
		0


(* Cherche un littéral dont la valeur est inconnue mais dont la négation n'apparaît pas dans current.
   Renvoie 0 si un tel littéral n'existe pas.                                                         *)
let find_single pos solution =
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


(* Cherche un littéral conséquence de current, i.e. présent dans une clause unitaire ou dont l'opposé
   n'apparait pas dans current.
   Renvoie 0 si un tel littéral n'existe pas.                                                         *)
let find_consequences current pos solution =
	let tmp = find_single pos solution in
	if tmp <> 0 then
		tmp
	else
		find_unit current solution


(* Effectue la boolean constraint propagation sur toutes les variables présentes sous une seule polarité
   ou présentes dans une clause unitaire.                                                                *)
let rec propa stack current pos solution print =
	let x = ref (find_consequences current pos solution) in
	while !x <> 0 do
		if solution.(0) < 0 then
			x := 0
		else
			begin
			print_conseq !x print ;
			if !x > 0 then
				(* x est nécessairement à vrai *)
				begin
				solution.(!x) <- 2 ;
				update !x stack current pos solution (snd pos.(!x)) (fst pos.(!x))
				end
			else
				(* x est nécessairement à faux *)
				begin
				solution.(- !x) <- -2 ;
				update !x stack current pos solution (fst pos.(- !x)) (snd pos.(- !x))
				end
			;
			x := find_consequences current pos solution ;
			end
	done




		(** PARIS ET BACKTRACKING **)


(* Effectue une étape de backtrack *)
let backtrack_step stack current pos solution k back print =
	
	(* Si la valeur de début de pile est positive et n'est pas issue d'une boolean constraint propagation,
	   donc pas nécessaire, on peut supposer l'opposé. On arrête alors le backtrack.                       *)
	if !k > 0 && solution.(!k) = 1 then
		begin
		solution.(0) <- 0 ;
		back := false ;
		k := backtrack stack current pos (snd pos.(!k)) ;	(* On retire !k *)
		print_backtrack !k solution.(abs !k) print ;
		k := - !k ;
		update !k stack current pos solution (fst pos.(- !k)) (snd pos.(- !k)) ;	(* On suppose l'opposé *)
		print_hyp !k print ;
		solution.(- !k) <- -1 ;
		end
	
	(* Sinon, il faut continuer le backtrack *)
	else
		begin
		if !k > 0 then
			k := backtrack stack current pos (snd pos.(!k))
		else
			k := backtrack stack current pos (fst pos.(- !k))
		;
		print_backtrack !k solution.(abs !k) print ;
		solution.(abs !k) <- 0 ;
		k := pick stack
		end



(* Implémente une itération de la boucle *)
let continue stack current pos solution k back print =
	
	(* On vient de découvrir la clause vide : on commence le backtrack *)
	if solution.(0) < 0 && not !back then
		begin
		k := pick stack ;		(* On a besoin de connaître la valeur à dépiler *)
		print_new_backtrack print ;
		back := true
		end
	
	(* Backtracking : on n'a pas encore pu faire de nouvelle hypothèse pour enlever la contradiction *)
	else if !back then
		backtrack_step stack current pos solution k back print	
	
	(* S'il n'y a pas de contradiction : on suppose par défaut la première variable libre comme vraie *)
	else
		begin
		k := abs !k + 1 ;
		if solution.(!k) = 0 then
			begin
			print_hyp !k print ;
			update !k stack current pos solution (snd pos.(!k)) (fst pos.(!k)) ;
			solution.(!k) <- 1 ;
			end
		end
