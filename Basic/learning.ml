open Cnf
open Array
open Dot

let nbr_blue c level current solution levels =
	let rec aux c lit =
		match c with
		| [] -> true, lit
		| x::q when x*solution.(abs x) < 0 && levels.(abs x) = level ->
			(*Printf.printf "%d\n" x ;*)
			if lit = 0 then
				aux q x
			(* A optimiser : il faudrait prendre celui qui a été mis à faux le plus récemment *)
			else if abs solution.(abs lit) > abs solution.(abs x) then
				false, lit
			else
				false, x
		| _::q ->
			aux q lit
	in
	aux c 0

let iter_learning graph clauses current solution levels start level =
	let pos_c = ref start in
	let c = ref clauses.(!pos_c) in
	let a, b = nbr_blue clauses.(!pos_c) level current solution levels in
	let fini = ref a in
	let lit = ref b in
	while (not !fini) do
		set_color (- !lit) Purple (Array.length solution) graph ;
		pos_c := (abs solution.(abs !lit)) - 2 ;
		c := fusion (List.filter (fun i -> i <> !lit) !c) (List.filter (fun i -> i <> - !lit) clauses.(!pos_c)) ;
		let a, b = nbr_blue !c level current solution levels in
		fini := a ; lit := b
	done ;
	set_color (- !lit) Yellow (Array.length solution) graph ;
	!c

let rec add pos_c graph current solution start level v =
	let rec aux l start =
		match l with
		| [] -> ()
		| (n,_)::q ->
			add_arete graph (-n, start) ;
			set_color (-n) White v graph ;
			aux q start
	in
	match current.(pos_c) with
	| _,_,[] -> ()
	| a,b,(n,l)::q when l = level ->
		add_arete graph (-n, start) ;
		set_color (-n) Blue v graph ;
		set_color start Blue v graph ;
		current.(pos_c) <- a,b,q ;		
		if abs solution.(abs n) > 1 then
			add ((abs solution.(abs n)) - 2) graph current solution (-n) level v ;
		add pos_c graph current solution start level v
	| a,b,q ->
		aux q start


let graph current solution level =
	let v = length solution - 1 in
	let g = creer_graph v in
	add (-solution.(0)-1) g current solution 0 level v ;
	set_color 0 Red v g ;
	g
	























