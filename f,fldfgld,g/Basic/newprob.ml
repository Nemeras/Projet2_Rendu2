open Printf
open DynArray
       
let rec print_clause buffer clause=
  match clause with
  |[]-> fprintf buffer "."
  |head::tail -> fprintf buffer "%d " head; print_clause buffer tail;;
  
let rec print_l buffer liste clauses=
  printf "tsdfsd\n";
  match liste with
  |[-1] -> printf "yolo\n";fprintf buffer "\n"
  |head::tail -> printf "yol\n";print_clause buffer (clauses.a.(head));print_l buffer tail clauses
  |_ -> printf "tdfg\n";failwith "bug in print_list";;
  
  
let create_new_cnf tableau_bonus clauses=
  let buffer = open_out "new.cnf" in
  fprintf buffer "p cnf 0 0\n";
  print_l buffer (tableau_bonus.a.(-1+tableau_bonus.length)) clauses;
  close_out buffer;;
  
