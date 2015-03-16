open Printf
open DynArray
       
(*let rec print_clause buffer clause=
  match clause with
  |[]-> fprintf buffer "."
  |head::tail -> fprintf buffer "%d " head; print_clause buffer tail;;*)
  
let rec print_l buffer liste clauses tableau_bonus=
  match liste with
  | [] -> ()
  | head::tail ->
	fprintf buffer "%s" (Cnf.string_of_clause (clauses.a.(head))) ;
	print_l buffer tableau_bonus.a.(head) clauses tableau_bonus ;
	print_l buffer tail clauses tableau_bonus
  
  
let create_new_cnf tableau_bonus clauses=
  let buffer = open_out "unsat.cnf" in
  fprintf buffer "p cnf 0 0\n";
  print_l buffer (tableau_bonus.a.(-1+tableau_bonus.length)) clauses tableau_bonus ;
  close_out buffer;;
  
