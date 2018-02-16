open DataTypes
open Expression
open List    

(* ===================================================== Reguły eliminacji =================================================== *)

let doubleNotE expr exprs = 
  exists (equal @@ Not (Not expr)) exprs 

let andlE expr exprs = 
  exists (equal expr) (map get_expr1 (filter is_and exprs)) 

let andrE expr exprs = 
  exists (equal expr) (map get_expr2 (filter is_and exprs)) 

let falseE expr exprs = 
  exists (equal False) exprs

let notE expr exprs = 
  exists (fun e' -> exists (equal @@ Not e') exprs) (filter (fun e' -> not(is_not e')) exprs)

let impE expr exprs = 
  let imp_list = filter (fun e' -> is_imp e' && equal (get_expr2 e') expr) exprs in
  let find_expr list = exists (fun e' -> exists (equal e') exprs) list in
  find_expr (map get_expr1 imp_list)

let orE expr exprs =
  let imp_list = filter (fun e' -> is_imp e' && equal (get_expr2 e') expr) exprs in
  let expr_pairs list = flatten @@ mapi (fun i e' -> mapi (fun j e'' -> (i,j, Or(get_expr1 e', get_expr1 e'') )) list) list in
  let find_Or list = exists (fun (i,j,e') -> if i <> j then exists (equal e') (filter is_or exprs) else false) list in
  find_Or (expr_pairs imp_list)

let eqvlE expr exprs =  
  let eqv_list = filter (fun e' -> is_eqv e' && equal (get_expr2 e') expr) exprs in
  let find_expr list = exists (fun e' -> exists (equal e') exprs) list in
  find_expr (map get_expr1 eqv_list) 

let eqvrE expr exprs =  
  let eqv_list = filter (fun e' -> is_eqv e' && equal (get_expr1 e') expr) exprs in
  let find_expr list = exists (fun e' -> exists (equal e') exprs) list in
  find_expr (map get_expr2 eqv_list)

let eqE expr exprs = 
  let eq_list = filter is_eq exprs in
  exists (fun (Eq (t1, t2) ) -> exists (fun e' -> equal (replace t1 t2 e') (replace t1 t2 expr)  ) exprs ) eq_list

let rec use expr exprs = 
  exists (fun f' -> f' expr exprs) [andlE; andrE; impE; orE; falseE; notE; eqvlE; eqvrE; doubleNotE; eqE]