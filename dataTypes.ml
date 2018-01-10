module PairMap = Map.Make(String)

exception SyntaxError of string 
exception DataTypesError of string * Lexing.position

(* ----------------------------------------------- Typ danych ------------------------------------------------------- *)

(* Reprezentacja wyrazen *)      
type 'a expression =
  (* funktory zdaniotwórcze *)
  | Or of  'a expression * 'a expression * 'a
  | And of 'a expression * 'a expression * 'a 
  | Not of 'a expression * 'a
  | Imp of 'a expression * 'a expression * 'a 
  | Eq of 'a expression * 'a expression * 'a
  (* formuła atomowa *) 
  | Atom of string * string list * (string * string) list * 'a
  (* referencja do axiomu / poprawnie udowodnionego wyrażenia*)
  | Ref of string * 'a
  (* kwantyfikatory *)
  | Forall of string * 'a expression * 'a
  | Exists of string * 'a expression * 'a
  (* symbole T i F *)
  | True of 'a
  | False of 'a 
  (* wyrażenie  z świeżą zmienną *)
  | Fresh of string * 'a expression * 'a

(* Reprezentacja elementów w dowodzie *)
type 'a proof =
  | Inset of 'a expression * ('a proof list) * 'a
  | FreshInset of string * 'a expression option * ('a proof list) * 'a
  | Expr of 'a expression

(* Wynik parsowania *)
type 'a typeCheckResult =
  | EOF
  | Error
  | Goal of string * 'a expression * 'a  proof list
  | Proof of 'a proof list
  | Axiom of string * 'a expression 

(* ----------------------------------------------- Akcesory -------------------------------------------------------- *)
let getPosition = function
  | And(_,_,p) | Or(_,_,p) | Imp(_,_,p) | Not(_,p) | Eq (_,_,p) | Atom (_,_,_,p) 
  | True p | False p | Ref(_,p) | Forall(_,_,p) | Exists (_,_,p) | Fresh(_,_,p) -> p

let getExpr1 = function
  | And(e,_,_) | Or(e,_,_) | Imp(e,_,_) | Eq (e,_,_) -> e 
  | e -> raise @@ DataTypesError ("Incorrect use of the function", getPosition e)

let getExpr2 = function
  | And(_,e,_) | Or(_,e,_) | Imp(_,e,_) | Eq (_,e,_) -> e 
  | e -> raise @@ DataTypesError ("Incorrect use of the function", getPosition e)

let getExpr = function
  | Not(e,_) | Forall(_,e,_) | Exists(_,e,_) | Fresh(_,e,_) -> e 
  | e -> raise @@ DataTypesError ("Incorrect use of the function", getPosition e)

let getName = function
  | Atom(name,_,_,_) | Ref (name,_)-> name 
  | e -> raise @@ DataTypesError ("Incorrect use of the function", getPosition e)

let getVars = function
  | Atom(_,vars,_,_) -> vars
  | e -> raise @@ DataTypesError ("Incorrect use of the function", getPosition e)

let getVariablesPair = function
  | Atom(_,_,vars,_) -> vars
  | e -> raise @@ DataTypesError ("Incorrect use of the function", getPosition e)

let getVar = function
  | Forall(v,_,_) | Exists(v,_,_) | Fresh(v,_,_) -> v
  | e -> raise @@ DataTypesError ("Incorrect use of the function", getPosition e)


(* ------------------------------------------- Tworzenie wyrażeń --------------------------------------------------- *)
let nullPosition = let open Lexing in {pos_fname= "null"; pos_lnum= 0; pos_bol= 0; pos_cnum= 0}
let createImp ?(p=nullPosition) expr1 expr2 = Imp(expr1,expr2,p) 
let createOr ?(p=nullPosition) expr1 expr2 = Or(expr1,expr2,p) 
let createAnd ?(p=nullPosition) expr1 expr2 = And(expr1,expr2,p)
let createEq ?(p=nullPosition) expr1 expr2 = Eq(expr1,expr2,p) 
let createNot ?(p=nullPosition) expr = Not(expr,p) 
let createAtom ?(p=nullPosition) name = Atom(name, [], [], p)
let createTrue ?(p=nullPosition) ()= True p 
let createFalse ?(p=nullPosition) ()= False p 
let createForall ?(p=nullPosition) var expr = Forall(var,expr,p) 
let createExists ?(p=nullPosition) var expr = Exists(var,expr,p)
let createFresh ?(p=nullPosition) vars expr = Fresh(vars,expr,p)

(* ----------------------------------------- Dopasowanie do wzorca ------------------------------------------------- *)
let isOr = function
  | Or(_,_,_) -> true
  | _ -> false

let isAnd = function
  | And(_,_,_) -> true
  | _ -> false

let isImp = function
  | Imp _-> true
  | _ -> false

let isNot= function
  | Not _-> true
  | _ -> false

let isAtom = function
  | Atom _ -> true
  | _ -> false

let isEq = function
  | Eq _ -> true
  | _ -> false

let isTrue = function
  | True _ -> true
  | _ -> false

let isFalse = function
  | False _ -> true
  | _ -> false

let isForall = function
  | Forall _-> true
  | _ -> false

let isExists = function
  | Exists _ -> true
  | _-> false

let isRef = function
  | Ref _ -> true
  | _ -> false

let isFresh = function
  | Fresh _ -> true
  | _ -> false

(* -------------------------------------- Operacje na strukturach danych -------------------------------------------- *)


(* ----------------------------------------- Rachunek kwantyfikatorów  ---------------------------------------------- *)
let rec get_replacement f = function 
  | Fresh (_,expr,_) | Not (expr,_) | Forall (_,expr,_) | Exists (_,expr,_) -> get_replacement f expr
  | Imp (expr1,expr2,pos) | Eq (expr1,expr2,pos) | Or (expr1,expr2,pos) | And (expr1,expr2,pos) -> begin
      match (get_replacement f expr1, get_replacement f expr2) with
      | Some x, Some y ->  if x = y then Some x else raise @@ DataTypesError ("Replaced variables do not agree", pos)
      | None, Some y -> Some y
      | Some x, None -> Some x
      | None, None -> raise @@  DataTypesError ("Variable not found", pos)
    end
  | Atom (_,_,vars,_) -> Some (List.find f vars)
  | _ -> None

let rec isVar x = function 
  | Fresh (_,expr,_) | Not (expr,_) | Forall (_,expr,_) | Exists (_,expr,_) -> isVar x expr
  | Imp (expr1,expr2,_) | Eq (expr1,expr2,_) | Or (expr1,expr2,_) | And (expr1,expr2,_) -> isVar x expr1 && isVar x expr2 
  | Atom (_,vars,_,_) -> List.mem x vars 
  | _ -> true

let getReplacedVar var expr = 
  try 
    match get_replacement (fun (x,y) -> y = var) expr with
    | Some (x,_) -> Some x
    | None -> None
  with  
  | Not_found -> None
  | DataTypesError _ -> None

let getReplacementVar var expr = 
  try 
    match get_replacement (fun (x,y) -> x = var) expr with
    | Some (_,y) -> Some y
    | None -> None
  with   
  | Not_found -> None
  | DataTypesError _ -> None

let isReplacedVar var expr = 
  match getReplacementVar var expr with 
  | None -> false
  | Some _ -> true

let isReplacementVar var expr =
  match getReplacedVar var expr with
  | Some _ -> true
  | None -> false

let rec removeVar x = function
  | Not (e,p) -> Not(removeVar x e,p)
  | Forall (v,e,p) -> Forall(v,removeVar x e,p) 
  | Exists (v,e,p) -> Exists(v,removeVar x e,p)
  | Fresh(v,e,p) -> Forall(v,removeVar x e,p) 
  | Imp (e1,e2,p) -> Imp(removeVar x e1, removeVar x e2, p)
  | Eq (e1,e2,p) -> Eq(removeVar x e1, removeVar x e2, p)
  | Or (e1,e2,p) -> Or(removeVar x e1, removeVar x e2, p)
  | And (e1,e2,p) -> And(removeVar x e1, removeVar x e2, p)
  | Atom (v, vars, reVars, p) -> 
    Atom(v, 
         List.fold_right (fun x' xs' -> if x = x' then xs' else x'::xs') vars [], 
         List.fold_right (fun (x',y') xs' -> if x = x' then xs' else (x',y')::xs') reVars [], 
         p) 
  | t -> t


let rec equals expr1 expr2 = 
  match (expr1,expr2) with 
  | Forall (v1, e1, _), Forall (v2, e2, _) | Exists (v1, e1, _), Exists (v2, e2, _) | Fresh (v1, e1, _), Fresh (v2, e2, _) -> 
    v1 = v2 && equals e1 e2 
  | And(e1,e2,_), And(e3,e4,_) | Or(e1,e2,_),Or(e3,e4,_) | Eq(e1,e2,_),Eq(e3,e4,_) ->  
    equals e1 e3 && equals e2 e4 || equals e1 e4 && equals e2 e3
  | Imp(e1,e2,_),Imp(e3,e4,_) ->  equals e1 e3 && equals e2 e4
  | Not(e1,_), Not(e2,_) -> equals e1 e2
  | Atom (id1,vars1,reVars1,_), Atom (id2,vars2,reVars2,_) -> 
    id1 = id2 && (List.sort compare vars1 ) = (List.sort compare vars2 ) && (List.sort compare reVars1 ) = (List.sort compare reVars2 )
  | False _, False _ -> true
  | True _, True _ -> true
  | Ref (id1,_), Ref (id2,_) -> id1 = id2
  | _ -> false

let rec show_formula = function 
  | Not (e,_) -> " ~" ^ show_formula e
  | Imp (e1,e2,_) -> "( " ^ (show_formula e1) ^ " => " ^ (show_formula e2) ^ ") "; 
  | Eq (e1,e2,_) ->  "( " ^ (show_formula e1) ^ " <=> " ^ (show_formula e2) ^ ") ";
  | Or (e1,e2,_) -> "( " ^ (show_formula e1) ^ " || " ^ (show_formula e2) ^ ") ";
  | And (e1,e2,_) -> "( " ^ (show_formula e1) ^ " && " ^ (show_formula e2) ^ ") ";
  | Atom (n,v1,v2,_) ->  n ^ "( " ^ List.fold_left (fun x y -> x ^ ", " ^ y ) "" v1 ^ ") " ^ "( " ^ (List.fold_left (fun xs (x,y) -> xs ^ x ^ " - " ^ y ^ ", ") "" v2) ^ ") " 
  | True _ -> "T"; 
  | False _ -> "F"
  | Forall(v,e,_) -> "V " ^ v ^ "." ^ show_formula e
  | Exists(v,e,_) -> "E " ^ v ^ "." ^ show_formula e
  | Ref (n,_) -> "ref " ^ n
  | Fresh(v,e,_) -> ">Fresh> " ^ v ^ "." ^ show_formula e

let rec show_proof = function
  | Inset(premise,proof,_) -> " [" ^ (show_formula premise) ^ ": " ^ (List.fold_left (fun x y -> x ^ show_proof y ^ "; ") "" proof) ^ "] " 
  | Expr formula -> show_formula formula
  | FreshInset(var, Some premise, proof, _) -> " [[" ^ var ^ "]" ^ (show_formula premise) ^ ": " ^ (List.fold_left (fun x y -> x ^ show_proof y ^ "; ") "" proof) ^ "] " 
  | FreshInset(var, None, proof, _) -> " [[" ^ var ^ "]" ^ ": " ^ (List.fold_left (fun x y -> x ^ show_proof y ^ "; ") "" proof) ^ "] " 

let show proofs = List.fold_left (fun x y -> x ^ show_proof y ^ "; ") "" proofs 