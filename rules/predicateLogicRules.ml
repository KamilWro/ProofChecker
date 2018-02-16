open DataTypes
open Expression
open List    


(* ====================================================== Logika I rzędu ===================================================== *)    

(* --------------------------------------------------- Funkcje pomocnicze ---------------------------------------------------- *)    

let check_type v t types = 
  mem_assoc v types && assoc v types = t 

let rec possible_replacement term expr =
  match term with
  | Function(id, terms) -> exists (fun t' -> not @@ possible_replacement t' expr) terms
  | Var var -> not(is_var var expr)

let replaced_term var expr fvar' expr' =  
  if snd var = snd fvar' && not(is_var (fst var) expr') && not(is_var (fst fvar') expr) then 
    try
      match replacement expr expr' with 
      | Some (Function _) -> false 
      | Some (Var v'') -> v'' = fst var 
      | None -> true
    with
    | Incorrect_Expressions -> false 
  else
    false

let exists_term var expr expr' types =
  try 
    match replacement expr' expr with
    | Some term' -> possible_replacement term' expr && not(is_var (fst var) expr') && check_type (get_id term') (snd var) types 
    | None -> check_type (fst var) (snd var) types 
  with
  | Incorrect_Expressions -> false 

(* -------------------------------------------------- Reguły wprowadzania ---------------------------------------------------- *)    

let existsI var expr exprs fexprs types = 
  exists (fun expr' -> exists_term var expr expr' types ) exprs || exists (fun (fvar', expr') -> replaced_term var expr fvar' expr') fexprs

let forallI var expr fexprs types = 
  exists (fun (fvar', expr') -> replaced_term fvar' expr' var expr) fexprs

let use_introduction_rules expr exprs fexprs types = 
  match expr with
  | Exists (x,expr') -> existsI x expr' exprs fexprs types
  | Forall (x,expr') -> forallI x expr' fexprs types 
  | _ -> false

(* -------------------------------------------------- Reguły eliminacji ------------------------------------------------------ *)

let forallE expr exprs types =
  exists (fun expr' -> exists_term (get_var expr') (get_expr expr') expr types) (filter is_forall exprs) 

let existsE expr exprs fexprs types = 
  let exists_list = filter is_exists exprs in
  let imp_list = filter (fun (_, expr') -> is_imp expr' && equal (get_expr2 expr') expr) fexprs in
  exists (fun ex' -> 
      exists (fun (fvar', imp') -> 
          replaced_term fvar' (get_expr1 imp') (get_var ex') (get_expr ex') ) imp_list ) exists_list     

let use_elimination_rules expr exprs fexprs types =
  forallE expr exprs types || existsE expr exprs fexprs types 

let use expr exprs fexprs types =
  use_introduction_rules expr exprs fexprs types || use_elimination_rules expr exprs fexprs types