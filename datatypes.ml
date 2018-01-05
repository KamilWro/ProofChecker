exception SyntaxError of string ;;
exception DataTypesError of string ;;

(* Reprezentacja wyrazen*)      
type 'a expression =
  | Or of  'a expression * 'a expression * 'a
  | And of 'a expression * 'a expression * 'a 
  | Not of 'a expression * 'a
  | Imp of 'a expression * 'a expression * 'a 
  | Eq of 'a expression * 'a expression * 'a 
  | Var of string * 'a
  | True of 'a
  | False of 'a 
;;

(* Reprezentacja elementów w dowodzie *)
type 'a proof =
  | Inset of 'a expression * ('a proof list)
  | Expr of 'a expression
;;

(* Wynik parsowania *)
type 'a typeCheckResult =
  | EOF
  | Error
  | Goal of string * 'a expression * 'a  proof list
  | Proof of 'a proof list
  | Axiom of string * 'a expression 
;;

(* ----------------------------------------------- Akcesory -------------------------------------------------------- *)

let getExpr1 = function
  | And(e,_,_) | Or(e,_,_) | Imp(e,_,_) | Eq (e,_,_) -> e 
  | _ -> raise @@ DataTypesError "This shouldnt happen"
;;

let getExpr2 = function
  | And(_,e,_) | Or(_,e,_) | Imp(_,e,_) | Eq (_,e,_) -> e 
  | _ -> raise @@ DataTypesError "This shouldnt happen"
;;

let getExpr = function
  | Not(e,_) -> e 
  | _ -> raise @@ DataTypesError "This shouldnt happen"
;;

let getName = function
  | Var(v,_) -> v 
  | _ -> raise @@ DataTypesError "This shouldnt happen"
;;

let getPosition = function
    And(_,_,pos) | Or(_,_,pos) | Imp(_,_,pos) | Not(_,pos) | Eq (_,_,pos) | Var (_,pos) | True pos | False pos -> pos 
;;     


(* ------------------------------------------- Tworzenie wyrażeń --------------------------------------------------- *)
let nullPosition = let open Lexing in {pos_fname= "null"; pos_lnum= 0; pos_bol= 0; pos_cnum= 0};;
let createImp ?(p=nullPosition) expr1 expr2 = Imp(expr1,expr2,p) ;;
let createOr ?(p=nullPosition) expr1 expr2 = Or(expr1,expr2,p) ;;
let createAnd ?(p=nullPosition) expr1 expr2 = And(expr1,expr2,p) ;;
let createEq ?(p=nullPosition) expr1 expr2 = Eq(expr1,expr2,p) ;;
let createNot ?(p=nullPosition) expr = Not(expr,p) ;;
let createVar ?(p=nullPosition) var = Var(var,p) ;;
let createTrue ?(p=nullPosition) ()= True p ;;
let createFalse ?(p=nullPosition) ()= False p ;;

(* ----------------------------------------- Dopasowanie do wzorca ------------------------------------------------- *)

let isOr = function
  | Or(_,_,_) -> true
  | _ -> false
;;

let isAnd = function
  | And(_,_,_) -> true
  | _ -> false
;;

let isImp = function
  | Imp(_,_,_) -> true
  | _ -> false
;;

let isNot= function
  | Not(_,_) -> true
  | _ -> false
;;

let isVar = function
  | Var(_,_) -> true
  | _ -> false
;;

let isEq = function
  | Eq(_,_,_) -> true
  | _ -> false
;;

let isTrue = function
  | True(_) -> true
  | _ -> false
;;

let isFalse = function
  | False(_) -> true
  | _ -> false
;;

(* -------------------------------------- Funkcje na strukturach danych -------------------------------------------- *)

let rec equals expr1 expr2 =
  match (expr1,expr2) with 
    And(e1,e2,_), And(e3,e4,_) | Or(e1,e2,_),Or(e3,e4,_) | Eq(e1,e2,_),Eq(e3,e4,_) -> 
    equals e1 e3 && equals e2 e4 || equals e1 e4 && equals e2 e3
  | Imp(e1,e2,_),Imp(e3,e4,_) ->  equals e1 e3 && equals e2 e4
  | Not(e1,_), Not(e2,_) -> equals e1 e2
  | Var (id1,_), Var (id2,_) -> id1 = id2
  | False _, False _ -> true
  | True _, True _ -> true
  | _ -> false
;;



let rec show_formula = function 
  | Not (expr,_) -> " ~" ^ show_formula expr
  | Imp (expr1,expr2,_) -> "( " ^ (show_formula expr1) ^ " => " ^ (show_formula expr2) ^ ") "; 
  | Eq (expr1,expr2,_) ->  "( " ^ (show_formula expr1) ^ " <=> " ^ (show_formula expr2) ^ ") ";
  | Or (expr1,expr2,_) -> "( " ^ (show_formula expr1) ^ " || " ^ (show_formula expr2) ^ ") ";
  | And (expr1,expr2,_) -> "( " ^ (show_formula expr1) ^ " && " ^ (show_formula expr2) ^ ") ";
  | Var (var,_) ->  var;
  | True _ -> "T";
  | False _ -> "F"
;;

let rec show_proof = function
  | Inset(premise,proof) -> " [" ^ (show_formula premise) ^ ": " ^ (List.fold_left (fun x y -> x ^ show_proof y ^ "; ") "" proof) ^ "] "; 
  | Expr formula -> show_formula formula;
;;

let show proofs = List.fold_left (fun x y -> x ^ show_proof y ^ "; ") "" proofs ;;