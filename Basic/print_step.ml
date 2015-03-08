			(** FONCTIONS D'AFFICHAGE **)



open List
open Array
open Printf

open Cnf



		(** RECAPITULATIF A CHAQUE ITERATION DE LA BOUCLE **)

let print_clauses current solution back =
	print_string "Contradiction : " ;
	if solution.(0) < 0 then
		print_string "Non.\n"
	else
		print_string "Oui.\n"
	;
	print_string "Backtrack : " ;
	if not back then
		print_string "Non.\n\n"
	else
		print_string "Oui.\n\n"
	;
	for i = 0 to length current - 1 do
		printf "Clause %d : " i ;
		let b, _, _ = current.(i) in
		if b then
			print_string "[INACTIVE]\t" ;
		let _, c, _ = current.(i) in
		print_string (string_of_clause c)
	done


let print_pos pos =
	for i = 1 to length pos - 1 do
		printf "Variable %d :\nLittéraux positifs : %sLittéraux négatifs : %s\n\n"
				i (string_of_clause (fst pos.(i))) (string_of_clause (snd pos.(i)))
	done


let print_step current solution back compt =
	printf "\n\n*************** \tEtape %d\t\t*****************\n\n" compt ;
	print_string "Solution courante :\n\t" ;
	print_instanciation solution ;
	print_string "\n\n\tEnsemble des clauses étudiées :\n\n" ;
	print_clauses current solution back ;
	print_string "\n\n"



		(** PARIS / CONSEQUENCES **)

let print_hyp k print =
	if print then
		printf "\t****  Hypothèse : %d  ****\n" k

let print_conseq k print =
	if print then
		printf "\t****  Déduction : %d  ****\n" k

let print_new_backtrack print =
	if print then
		begin
		printf "\t****  Contradiction-  ****\n" ;
		printf "\t**** Début  Backtrack ****\n"
		end

let print_backtrack k value print =
	if print then
		begin
		printf "\t****  Backtrack : %d  ****\n" k ;
		if abs value > 2 then
			print_string "\t[Ancienne déduction]\n" ;
		if abs value > 2 || k < 0 then
			print_string "\t Le backtrack continue...\n"
		end
