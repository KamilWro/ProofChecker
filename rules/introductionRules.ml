open DataTypes
open Expression
open List

(* ==================================================== Reguły wprowadzenia ================================================== *)

let impI expr exprs = 
  exists (equal expr) exprs 

let andI expr exprs = 
  exists (equal @@ get_expr1 expr) exprs && exists (equal (get_expr2 expr)) exprs

let orlI expr exprs = 
  exists (equal @@ get_expr1 expr) exprs

let orrI expr exprs = 
  exists (equal @@ get_expr2 expr) exprs

let notI expr exprs = 
  exists (equal @@ Imp (get_expr expr, False)) exprs

let eqvI expr exprs = 
  exists (equal @@ Imp(get_expr1 expr, get_expr2 expr)) exprs && 
  exists (equal @@ Imp(get_expr2 expr, get_expr1 expr)) exprs 

let eqI expr = 
  get_term1 expr = get_term2 expr 

let rec use expr exprs = 
  match expr with 
  | Imp _ -> impI expr exprs  
  | And _ -> andI expr exprs 
  | Or _ -> orlI expr exprs  || orrI expr exprs 
  | Eqv _ -> eqvI expr exprs   
  | Not _ -> notI expr exprs   
  | True _ -> true
  | Eq _ -> eqI expr
  | _ -> false