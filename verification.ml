open DataTypes
open Expression
open List

exception Incorrect_Proof of string * Lexing.position
exception No_Proof of string
exception No_value 

let ex pos x = 
  raise @@ Incorrect_Proof (x^": is fresh variable", pos) 

let bind m f g = match m with 
  | None -> g 
  | Some x -> f x

let get = function
  | Some x -> x
  | None -> raise No_value

(* ================================================= Poprawność użycia zmiennych ============================================= *)

let rec get_fvar_t fvars = function
  | Var v -> if mem v fvars then Some v else None
  | Function (_,terms) ->
    try find is_some (map (fun t -> get_fvar_t fvars t) terms) with
    | Not_found -> None

let rec get_fvar fvars = function
  | Not (e) -> get_fvar fvars e
  | Imp (e1, e2)
  | Or (e1, e2)  
  | And (e1, e2) 
  | Eqv (e1, e2) -> bind (get_fvar fvars e1) (fun x -> Some x) (get_fvar fvars e2) 
  | Exists (v, e) 
  | Forall (v, e) -> if mem (fst v) fvars then Some (fst v) else get_fvar fvars e
  | Eq (t1, t2) -> bind (get_fvar_t fvars t1) (fun x -> Some x) (get_fvar_t fvars t2) 
  | True
  | False -> None 
  | Atom (_, terms) ->
    try find is_some (map (fun t -> get_fvar_t fvars t) terms) with
    | Not_found -> None

let rec check_fvar proof fvars old_fvars sc = 
  match proof with
  | [] ->  raise @@ No_Proof ("Expected proof of the expression")
  | Expr(expr, pos)::[] -> bind (get_fvar old_fvars expr) (ex pos) (sc expr)
  | Expr(expr, pos)::xs ->  bind (get_fvar old_fvars expr) (ex pos) (check_fvar xs fvars old_fvars sc)
  | Fresh_Inset(fvar, _, _, pos)::_ when List.mem (fst fvar) fvars ->  raise @@ Incorrect_Proof ("Expected fresh variables", pos) 
  | Inset(assumption, proof,pos)::xs -> 
    bind (get_fvar old_fvars assumption) (ex pos) (check_fvar proof fvars old_fvars (fun _ -> check_fvar xs fvars old_fvars sc))
  | Fresh_Inset(fvar, None, proof, pos)::xs ->  
    check_fvar proof (fst fvar::fvars) old_fvars (fun _ -> check_fvar xs fvars (fst fvar::old_fvars) sc)
  | Fresh_Inset(fvar, Some assumption, proof, pos)::xs ->  
    bind (get_fvar old_fvars assumption) (ex pos) 
      (check_fvar proof (fst fvar::fvars) old_fvars (fun _ -> check_fvar xs fvars (fst fvar::old_fvars) sc))  

let run expr proof = 
  match expr with 
  | None -> check_fvar proof [] [] (fun _ -> true)  
  | Some e -> 
    let sc e' = if equal e' e then true else raise @@ No_Proof ("Expected proof of the expression") in
    check_fvar proof [] [] sc

