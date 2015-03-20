open Printf
open DynArray
open Pervasives

 
let rec print_l buffer liste clauses =
match liste with
|[] -> fprintf buffer "\n\n\n";
|head::tail -> fprintf buffer "%s" (Cnf.string_of_clause (clauses.a.(head)));print_l buffer tail clauses;;
  
let create_new_cnf tableau_bonus clauses =
  let new_buffer = open_out "unsat.cnf" in 
  fprintf new_buffer "p cnf 0 0\n";
  for i=0 to ((tableau_bonus.length)-1) do
    if tableau_bonus.a.(i) <> [] then
      begin
	fprintf new_buffer "c La clause\n";
	fprintf new_buffer "%s" (Cnf.string_of_clause (clauses.a.(i)));
	fprintf new_buffer "c engendree avec les clauses : ";
	print_l new_buffer (tableau_bonus.a.(i)) clauses;
      end;
  done;
  close_out new_buffer
