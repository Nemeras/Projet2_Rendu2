type 'a dynarray = {mutable a : 'a array; mutable length : int};;
  
let make l cst= {a=Array.make l cst ;length= l};;

let func_add dyn i =
match i with
|i when i < (Array.length dyn.a) -> dyn.a.(i)
|i -> [];;

let add dyn element=
if dyn.length = (Array.length dyn.a) then 
	dyn.a <- Array.init (1+2*dyn.length) (func_add dyn);
dyn.a.(dyn.length) <- element;
dyn.length <- 1+dyn.length;;
