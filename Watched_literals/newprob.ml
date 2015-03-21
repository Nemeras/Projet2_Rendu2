open Printf
open DynArray
open Pervasives

 
let rec print_l buffer tableau_bonus start clauses solution l =
	let rec aux2 liste =
		match liste with
		| [] -> ()
		| head::tail ->
			print_l buffer tableau_bonus head clauses solution l ;
			aux2 tail
	in
	let rec aux c =
		match c with
		| [] ->
			aux2 tableau_bonus.a.(start) ;
			clauses.a.(start) <- [0]
		| x::c2 when x*solution.(abs x) < 0 ->
			aux c2 ;
			print_l buffer tableau_bonus ((abs solution.(abs x)) - 2) clauses solution l
		| _::c2 -> aux c2
	in
	if start < l && clauses.a.(start) <> [0] then
		fprintf buffer "%s" (Cnf.string_of_clause clauses.a.(start)) ;
	aux clauses.a.(start)
  
let create_new_cnf tableau_bonus clauses solution l =
	let new_buffer = open_out "unsat.cnf" in 
	fprintf new_buffer "p cnf 0 0\n";
	print_l new_buffer tableau_bonus (-solution.(0)-1) clauses solution l ;
	(*print_l new_buffer tableau_bonus (clauses.length-1) clauses solution l ;*)
	close_out new_buffer
