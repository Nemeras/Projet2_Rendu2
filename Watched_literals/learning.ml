open Cnf
open Array
open Dot
open DynArray

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

let iter_learning bonus graph clauses current solution levels orders start level activate tableau_bonus =
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
	!c, !lit


let rec add pos_c graph current solution levels orders seen start level v =
	let rec aux l start =
		match l with
		| [] -> ()
		| n::q ->
			if not seen.(abs start) then
				begin
				add_arete graph (-n, start) ;
				set_color (-n) White v graph ;
				aux q start
			end
	in
	let rec princ l start =
		match l with
		| n::q when n*solution.(abs n) < 0 && levels.(abs n) = level && (start = 0 || orders.(abs n) <= orders.(abs start)) ->
			add_arete graph (-n, start) ;
			set_color (-n) Blue v graph ;
			if abs solution.(abs n) > 1 then
				add ((abs solution.(abs n)) - 2) graph current solution levels orders seen (-n) level v ;
			princ q start
		| n::q when n*solution.(abs n) >= 0 || levels.(abs n) = level ->
			princ q start
		| _ ->
			if start = 0 || abs solution.(abs start) > 1 then
				aux l start ;
			seen.(abs start) <- true
	in
	if not seen.(abs start) then
		princ current.a.(pos_c) start


let graph current solution levels orders level activate =
	let v = if activate then length solution - 1 else 0 in
	let g = creer_graph v in
	if activate then
		begin
		let seen = Array.make (length solution) false in
		add (-solution.(0)-1) g current solution levels orders seen 0 level v
		end ;
	g
























