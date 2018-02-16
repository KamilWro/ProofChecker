exception Syntax_Error of string 
exception Data_Types_Error of string

(* =================================================== Typ danych =================================================== *)

(* Reprezentacja termów *)   
type term = 
  | Function of string * term list 
  | Var of string 

type variable = string * string option

(* Reprezentacja formuł *)      
type expression =
  | Or of  expression * expression 
  | And of expression * expression 
  | Not of expression 
  | Imp of expression * expression 
  | Eqv of expression * expression
  | Eq of term * term
  | Atom of string * term list
  | True 
  | False
  | Forall of variable * expression
  | Exists of variable * expression

(* Reprezentacja elementów w dowodzie *)
type 'a proof =
  | Inset of expression * ('a proof list) * 'a
  | Fresh_Inset of variable * expression option * ('a proof list) * 'a
  | Expr of expression * 'a

(* Wynik parsowania *)
type 'a type_check_result =
  | EOF
  | Error
  | Goal of string * expression * 'a proof list
  | Proof of 'a proof list
  | Axiom of expression
  | Type of string * string 

(* =================================================== Akcesory =================================================== *)

let get_position = function
  | Inset(_, _, p) -> p
  | Expr (_, p) -> p
  | Fresh_Inset(_, _, _, p) -> p


let get_expr1 = function
  | And(e,_) 
  | Or(e,_) 
  | Imp(e,_) 
  | Eqv (e,_) -> e 
  | _ -> raise @@ Data_Types_Error ("Incorrect use of the function get_expr1")

let get_expr2 = function
  | And(_,e) 
  | Or(_,e) 
  | Imp(_,e) 
  | Eqv (_,e) -> e 
  | _ -> raise @@ Data_Types_Error ("Incorrect use of the function 'get_expr2'")

let get_expr = function
  | Not(e) 
  | Forall(_,e) 
  | Exists(_,e) -> e 
  | _ -> raise @@ Data_Types_Error ("Incorrect use of the function 'get_expr'")

let get_id = function
  | Atom(name,_) -> name 
  | _ -> raise @@ Data_Types_Error ("Incorrect use of the function 'get_name'")

let get_terms = function
  | Atom(_,terms) -> terms
  | _ -> raise @@ Data_Types_Error ("Incorrect use of the function 'get_terms'")

let get_var = function
  | Forall(v,_) 
  | Exists(v,_)  -> v
  | _ -> raise @@ Data_Types_Error ("Incorrect use of the function 'get_var'")

let get_term1 = function
  | Eq(t,_) -> t
  | e -> raise @@ Data_Types_Error ("Incorrect use of the function 'get_term1'")

let get_term2 = function
  | Eq(_,t) -> t
  | e -> raise @@ Data_Types_Error ("Incorrect use of the function 'get_term2'")

let get_id = function
  | Function(id,_)
  | Var id -> id


(* ============================================= Dopasowanie do wzorca ============================================= *)

let is_or = function
  | Or _ -> true
  | _ -> false

let is_and = function
  | And _ -> true
  | _ -> false

let is_imp = function
  | Imp _-> true
  | _ -> false

let is_not= function
  | Not _-> true
  | _ -> false

let is_atom = function
  | Atom _ -> true
  | _ -> false

let is_eqv = function
  | Eqv _ -> true
  | _ -> false

let is_true = function
  | True -> true
  | _ -> false

let is_false = function
  | False -> true
  | _ -> false

let is_forall = function
  | Forall _-> true
  | _ -> false

let is_exists = function
  | Exists _ -> true
  | _-> false

let is_eq = function
  | Eq _ -> true
  | _ -> false
