open Cnf
open Array
open Dot

let nbr_blue c level current solution levels orders =
	let rec aux c lit found =
		match c with
		| [] -> found <= 1, lit
		| x::q when x*solution.(abs x) < 0 && levels.(abs x) = level ->
			if found = 0 then
				aux q x 1
			else if orders.(abs lit) > orders.(abs x) then
				aux q lit (found + 1)
			else
				aux q x (found + 1)
		| _::q ->
			aux q lit found
	in
	aux c 0 0

let iter_learning graph clauses current solution levels orders start level activate =
	print_int start ; print_newline() ;
	let pos_c = ref start in
	let c = ref clauses.(!pos_c) in
	let a, b = nbr_blue clauses.(!pos_c) level current solution levels orders in
	let fini = ref a in
	let lit = ref b in
	while (not !fini) do
		if activate then
			set_color (- !lit) Purple (Array.length solution - 1) graph ;
		pos_c := (abs solution.(abs !lit)) - 2 ;
		c := fusion (List.filter (fun i -> i <> !lit) !c) (List.filter (fun i -> i <> - !lit) clauses.(!pos_c)) ;
		let a, b = nbr_blue !c level current solution levels orders in
		fini := a ;
		lit := b ;
	(*print_string (Cnf.string_of_clause !c) ;
	print_int !lit ; print_newline() ;*)
	done ;
	if activate then
		set_color (- !lit) Yellow (Array.length solution - 1) graph ;
	!c


let rec add pos_c graph current solution levels orders start level v =
	let rec aux l start =
		match l with
		| [] -> ()
		| n::q ->
			add_arete graph (-n, start) ;
			set_color (-n) White v graph ;
			aux q start
	in
	let rec princ l start =
		match l with
		| [] -> ()
		| n::q when n*solution.(abs n) < 0 && levels.(abs n) = level && (start = 0 || orders.(abs n) <= orders.(abs start)) ->
			add_arete graph (-n, start) ;
			set_color (-n) Blue v graph ;
			if abs solution.(abs n) > 1 then
				add ((abs solution.(abs n)) - 2) graph current solution levels orders (-n) level v ;
			princ q start
		| n::q when solution.(abs n) >= 0 || levels.(abs n) = level ->
			princ q start
		| _ ->
			aux l start
	in
	princ current.(pos_c) start


let graph current solution levels orders level activate =
	let v = if activate then length solution - 1 else 0 in
	let g = creer_graph v in
	if activate then
		add (-solution.(0)-1) g current solution levels orders 0 level v ;
	g
























