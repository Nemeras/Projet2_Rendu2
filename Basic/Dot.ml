open Printf

type listearete = (int*int) list;;
type couleur =
Red
| Blue
| White
| None
| Purple
| Yellow;;

type tableaucouleur = couleur array;;

type graph = {mutable a: listearete;mutable c: tableaucouleur};;

let creer_graph nb_variables = {a=[];c=Array.make (1+2*nb_variables) None};;

let add_arete graph arete = graph.a<-arete::(graph.a);;

let changer_var variable nb_variables = if variable >= 0 then variable else (nb_variables+(abs variable));;

let var_changer variable nb_variables = if variable <= nb_variables then variable else -(variable-nb_variables);;

let set_color variable couleur nb_variables graph=
let var = changer_var variable nb_variables in
graph.c.(var) <- couleur;;

let rec compile_liste liste buffer=
match liste with
|[]->();
|(sommet1,sommet2)::tail->(fprintf buffer "%d -> %d;\n" sommet1 sommet2);compile_liste tail buffer;
|_-> failwith "probleme dans compile_liste";;

let compile_color tc buffer nb_variables=
fprintf buffer " 0 [label=\"conflict\",style=filled,color=crimson]; \n";
for i = 1 to ((Array.length tc)-1) do
  let nb = var_changer i nb_variables in
    match (tc.(i)) with
    |None -> ();
    |Blue -> fprintf buffer "%d [label=\"%d\",style=filled,color=\"cornflowerblue\"];\n" nb nb;
    |White -> fprintf buffer "%d [label=\"%d\",style=filled,color=\"ghostwhite\"];\n" nb nb; 
    |Purple -> fprintf buffer "%d [label=\"%d\",style=filled,color=\"darkorchid1\"];\n" nb nb; 
    |Yellow -> fprintf buffer "%d [label=\"%d\",style=filled,color=\"gold\"];\n" nb nb; 
    |_-> failwith "probleme dans compile_color";
done;
fprintf buffer "}";;

let compile graph nb_variables=
  let buffer = open_out("graph.dot") in
fprintf buffer "digraph G {\n size =\"4,4\";\n";
compile_liste graph.a buffer;
compile_color graph.c buffer nb_variables;
fprintf stdout "YOLO"
;;

(*let functest i= match i with
  |0 -> Red
  |1 -> Blue
  |2 -> Yellow
  |3 -> Purple
  |4 -> White;;

let arraytest=Array.init 5 functest;;

let aretetest = (-2,2)::(-1,1)::(-2,0)::(-1,0)::[];;

let graphtest = {a=aretetest;c=arraytest};;

let _ = compile graphtest 2;;*)
