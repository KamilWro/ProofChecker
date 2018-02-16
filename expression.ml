open List
open DataTypes
exception Incorrect_Expressions

let get_options v1 v2  = 
  match (v1, v2) with
  | Some x, Some y -> if x = y then Some x else raise @@ Incorrect_Expressions
  | None, Some x -> Some x
  | Some x, None -> Some x
  | None, None -> None 

let is_some = function Some _ -> true | None -> false

(* =============================================================== termy =============================================================== *)
let rec replacement_t t1 t2 = 
  match (t1, t2) with
  | Function (id, terms), Function (id', terms') when id = id' && length terms = length terms' ->  replacement_from_list terms terms'
  | Var var, Var var' -> if var = var' then None else Some t1      
  | _ -> Some t1

and replacement_from_list terms terms' = 
  match filter is_some @@ map (fun (t1,t2) -> replacement_t t1 t2) (combine terms terms') with
  | [] -> None
  | x :: xs -> if for_all (fun x' -> x' = x) xs then x else raise Incorrect_Expressions  

let rec replace_t term1 term2 = function
  | Function(id,terms) -> Function(id, map (fun t -> if t = term1 then term2 else t) terms)
  | t -> if term1 = t then term2 else t  

let rec adjust_t map term1 term2 types =
  match (term1, term2) with
  | Function(id, terms), Function(id', terms') when id = id' && length terms = length terms' ->  
    fold_left (fun result (t1, t2) -> result && adjust_t map t1 t2 types) true (combine terms terms')  
  | Function(id,[]), Var var -> mem_assoc id types && mem_assoc var types && assoc id types = assoc var types
  | Var var, Var var' -> exists (fun (v', v) -> var' = v' && var = v) map  
  | _ -> false

let rec is_var_t v = function
  | Var var -> var = v
  | Function (_, terms) -> exists (fun t -> is_var_t v t) terms 

(* ================================================= wyrażenia (formuły atomowe) ======================================================= *)

let rec replacement expr1 expr2 = 
  match (expr1, expr2) with
  | Not (e), Not(e') -> replacement e e'
  | Eqv (e1, e2), Eqv (e1', e2') 
  | Or (e1, e2), Or (e1', e2') 
  | And (e1, e2), And (e1', e2') 
  | Imp (e1, e2), Imp (e1', e2') -> get_options (replacement e1 e1') (replacement e2 e2') 
  | Atom (id,terms), Atom (id',terms') when id = id' && length terms = length terms' -> replacement_from_list terms terms'
  | Forall (v, e), Forall (v', e') 
  | Exists (v, e), Exists (v', e') when v = v' -> replacement e e'
  | Eq(t1, t2), Eq(t1', t2') ->  get_options (replacement_t t1 t1') (replacement_t t2 t2')
  | True, True 
  | False, False -> None
  | _ -> raise Incorrect_Expressions

let rec equal expr1 expr2 = 
  match (expr1,expr2) with 
  | Forall (v, e), Forall (v', e') 
  | Exists (v, e), Exists (v', e') -> v = v' && equal e e' 
  | And(e1, e2), And(e1', e2') 
  | Or(e1, e2), Or(e1', e2') 
  | Eqv(e1, e2), Eqv(e1', e2') ->  equal e1 e1' && equal e2 e2' || equal e1 e2' && equal e2 e1'
  | Imp(e1,e2),Imp(e1',e2') ->  equal e1 e1' && equal e2 e2'
  | Not(e), Not(e') -> equal e e'
  | Atom (id, terms), Atom (id', terms') -> id = id' && terms = terms'
  | False, False -> true
  | True, True -> true
  | Eq(t1, t2), Eq(t1', t2') -> t1 = t1' && t2 = t2' || t1 = t2' && t2 = t1'
  | _ -> false

let rec replace term1 term2 = function
  | Not (e) -> Not(replace term1 term2 e)
  | Imp (e1, e2) -> Imp(replace term1 term2 e1, replace term1 term2 e2)
  | Eqv (e1, e2) -> Eqv(replace term1 term2 e1, replace term1 term2 e2)
  | Or (e1, e2) -> Or(replace term1 term2 e1, replace term1 term2 e2)
  | And (e1, e2) -> And(replace term1 term2 e1, replace term1 term2 e2)
  | Forall (v, e) -> Forall(v, replace term1 term2 e)
  | Exists (v, e) -> Exists(v, replace term1 term2 e)
  | Eq(t1, t2) when term1 = t1 ->  Eq(term2, t2)
  | Eq(t1, t2) when term1 = t2 ->  Eq(t1, term2)
  | Eq(t1, t2) -> Eq(replace_t term1 term2 t1, replace_t term1 term2 t2)
  | Atom(id,terms) -> Atom(id, map (fun t -> if t = term1 then term2 else t) terms)
  | e -> e                          

let rec is_var v = function 
  | Not (e) -> is_var v e
  | Eqv (e1, e2) 
  | Or (e1, e2) 
  | And (e1, e2) 
  | Imp (e1, e2) -> is_var v e1 || is_var v e2
  | Exists ((v',_), e) 
  | Forall ((v',_), e) when v' = v -> is_var v e
  | Eq(t1, t2) -> is_var_t v t1 || is_var_t v t2
  | Atom(id,terms) -> exists (fun t -> is_var_t v t) terms 
  | _ -> false   

let rec adjust map expr1 expr2 types sc =
  match (expr1, expr2) with
  | Forall ((v, t), e), Forall ((v', t'), e') 
  | Exists ((v, t), e), Exists ((v', t'), e')  -> t = t' && adjust ((v',v)::map) e e' ((v',t')::types) sc
  | And(e1, e2), And(e1', e2') 
  | Or(e1, e2), Or(e1', e2') 
  | Eqv(e1, e2), Eqv(e1', e2') -> 
    adjust map e1 e1' types (fun map' -> adjust map' e2 e2' types sc) || adjust map e1 e2' types (fun map' -> adjust map' e2 e1' types sc) 
  | Imp(e1, e2), Imp(e1', e2') -> adjust map e1 e1' types (fun map' -> adjust map' e2 e2' types sc) 
  | Not(e), Not(e') -> adjust map e e' types sc
  | False, False  
  | True, True -> sc map
  | Eq(t1, t2), Eq(t1', t2') -> 
    adjust_t map t1 t1' types && adjust_t map t2 t2' types || adjust_t map t1 t2' types && adjust_t map t2 t1' types
  | Atom (id, terms), Atom (id', terms') when length terms = length terms' 
                                           && (not(List.mem_assoc id' map) || exists (fun (v', v) -> id' = v' && id = v) map) ->  
    for_all (fun (t1, t2) -> adjust_t map t1 t2 types) (combine terms terms')     
  | _ -> false                    

let rec eq expr1 expr2 types =
  try adjust [] expr1 expr2 types (fun _ -> true) with
  | _ -> false