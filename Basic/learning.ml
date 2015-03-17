open Cnf
open Array
open Dot

open DynArray

let nbr_blue c level current solution levels orders =
	let rec aux c lit =
		match c with
		| [] -> true, lit
		| x::q when x*solution.(abs x) < 0 && levels.(abs x) = level ->
			(*Printf.printf "%d\n" x ;*)
			if lit = 0 then
				aux q x
			else if (*abs solution.(abs lit) > abs solution.(abs x)*) orders.(abs lit) > orders.(abs x) then
				false, lit
			else
				false, x
		| _::q ->
			aux q lit
	in
	aux c 0

let iter_learning bonus graph clauses current solution levels orders start level activate tableau_bonus=
	let pos_c = ref start in
	let c = ref clauses.a.(!pos_c) in
	if bonus then 
		begin
			DynArray.add tableau_bonus [] [];
			tableau_bonus.a.(tableau_bonus.length-1) <- (!pos_c)::(tableau_bonus.a.(tableau_bonus.length-1));
		end;
	let a, b = nbr_blue clauses.a.(!pos_c) level current solution levels orders in
	let fini = ref a in
	let lit = ref b in

	while (not !fini) do
		if activate then
			set_color (- !lit) Purple (Array.length solution - 1) graph ;
		pos_c := (abs solution.(abs !lit)) - 2 ;
		c := fusion (List.filter (fun i -> i <> !lit) !c) (List.filter (fun i -> i <> - !lit) clauses.a.(!pos_c)) ;
		if bonus then
			tableau_bonus.a.(tableau_bonus.length-1) <- (!pos_c)::(tableau_bonus.a.(tableau_bonus.length-1));
		let a, b = nbr_blue !c level current solution levels orders in
		fini := a ;
		lit := b
	done ;
	if activate then
		set_color (- !lit) Yellow (Array.length solution - 1) graph ;
	(*print_string (Cnf.string_of_clause !c) ;*)
	!c, !lit


let rec add pos_c graph current solution start level v =
	let rec aux l start =
		match l with
		| [] -> ()
		| (n,_)::q ->
			 add_arete graph (-n, start) ;
			 set_color (-n) White v graph ;
			 aux q start
	in
	match current.a.(pos_c) with
	| _,_,[] -> ()
	| a,b,(n,l)::q when l = level ->
		 add_arete graph (-n, start) ;
		 set_color (-n) Blue v graph ;
		 current.a.(pos_c) <- a,b,q ;
		 if abs solution.(abs n) > 1 then
			 add ((abs solution.(abs n)) - 2) graph current solution (-n) level v ;
		 add pos_c graph current solution start level v
	| a,b,q ->
		 aux q start
	 
	 
let graph current solution level activate =
	let v = if activate then length solution - 1 else 0 in
	let g = creer_graph v in
	if activate then
		add (-solution.(0)-1) g current solution 0 level v ;
	g
























