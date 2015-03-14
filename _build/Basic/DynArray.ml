type 'a dynarray = {mutable a : 'a array; mutable length : int};;
  
let make l cst= {a=Array.make l cst ;length= l};;

let func_add dyn cst i=
match i with
|i when i < (Array.length dyn.a) -> dyn.a.(i)
|i -> cst;;

let add dyn element cst=
if dyn.length = (Array.length dyn.a) then 
        begin
	  let dyn2 = Array.init (1+2*dyn.length) (fun i -> func_add dyn cst i) in
	  dyn.a <- dyn2;
	end;
 dyn.a.(dyn.length) <- element;
 dyn.length <- 1+dyn.length;;
