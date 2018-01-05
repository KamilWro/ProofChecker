module PairMap = Map.Make(StringMap)
open Datatypes
open Lexing

exception IncorrectProof of string

let elem x list1 list2 = List.exists (equals x) list1 || List.exists (equals x) list2;;

(* ---------------------------------------------------- Reguły wprowadzenia ------------------------------------------------- *)

let impI expr premises conclusions = elem expr premises conclusions ;; 
let andI expr premises conclusions = elem (getExpr1 expr) premises conclusions && elem (getExpr2 expr) premises conclusions ;;
let orlI expr premises conclusions = elem (getExpr1 expr) premises conclusions ;;
let orrI expr premises conclusions = elem (getExpr2 expr) premises conclusions ;;
let notI expr premises conclusions = elem (createImp (getExpr expr) (createFalse())) premises conclusions ;;
let eqI expr premises conclusions = elem (createImp (getExpr1 expr) (getExpr2 expr)) premises conclusions && 
                                    elem (createImp (getExpr2 expr) (getExpr1 expr)) premises conclusions
;;

let rec useIntroductionRule premises conclusions = function
  | expr when isImp expr && impI expr premises conclusions -> true 
  | expr when isAnd expr && andI expr premises conclusions -> true 
  | expr when isOr expr && orlI expr premises conclusions -> true 
  | expr when isOr expr && orrI expr premises conclusions -> true 
  | expr when isEq expr && eqI expr premises conclusions -> true   
  | expr when isNot expr && notI expr premises conclusions -> true  
  | expr when isTrue expr -> true
  | _ -> false
;;

(* ----------------------------------------------------- Reguły eliminacji -------------------------------------------------- *)

let doubleNotE expr premises conclusions = elem (createNot (createNot expr)) premises conclusions ;;
let andlE expr premises conclusions = let open List in elem expr (map getExpr1 (filter isAnd premises)) (map getExpr1 (filter isAnd conclusions)) ;;
let andrE expr premises conclusions = let open List in elem expr (map getExpr2 (filter isAnd premises)) (map getExpr2 (filter isAnd conclusions)) ;;
let falseE expr premises conclusions = elem (createFalse()) premises conclusions ;;

let impE expr premises conclusions =
  let open List in  
  let getImpList list = filter (fun x -> isImp x && equals (getExpr2 x) expr) list in
  let findExpr list = exists (fun x -> elem x premises conclusions) list in
  findExpr (map getExpr1 (getImpList premises)) || findExpr (map getExpr1 (getImpList conclusions));
;;

let orE expr premises conclusions =
  let open List in 
  let getImpList list = filter (fun x -> isImp x && equals (getExpr2 x) expr) list in
  let getExprPairs list = flatten @@ mapi (fun i x -> mapi (fun j y -> (i,j,createOr (getExpr1 x) (getExpr1 y) )) list) list in
  let findOrExpr list = exists (fun (i,j,x) -> if i <> j then elem x (filter isOr premises) (filter isOr conclusions) else false) list in
  findOrExpr (getExprPairs (getImpList premises)) || findOrExpr (getExprPairs (getImpList conclusions))
;;

let notE expr premises conclusions = 
  let findExpr list = List.exists (fun x -> elem (createNot x) premises conclusions) (List.filter (fun x -> not(isNot x)) list) in
  findExpr premises || findExpr conclusions
;;

let eqlE expr premises conclusions = 
  let open List in  
  let getEqList list = filter (fun x -> isEq x && equals (getExpr2 x) expr) list in
  let findExpr list = exists (fun x -> elem x premises conclusions) list in
  findExpr (map getExpr1 (getEqList premises)) || findExpr (map getExpr1 (getEqList conclusions))
;;

let eqrE expr premises conclusions = 
  let open List in  
  let getEqList list = filter (fun x -> isEq x && equals (getExpr1 x) expr) list in
  let findExpr list = exists (fun x -> elem x premises conclusions) list in
  findExpr (map getExpr2 (getEqList premises)) || findExpr (map getExpr2 (getEqList conclusions))
;;

let rec useEliminationRule premises conclusions = function
  | expr when andlE expr premises conclusions  -> true 
  | expr when andrE expr premises conclusions  -> true 
  | expr when impE expr premises conclusions  -> true 
  | expr when orE expr premises conclusions  -> true 
  | expr when falseE expr premises conclusions  -> true 
  | expr when notE expr premises conclusions  -> true
  | expr when doubleNotE expr premises conclusions  -> true
  | _ -> false
;;

(* -------------------------------------------------------- Dowodzenie ------------------------------------------------------ *)    

(* Pomysł że tym znakiem zapytania :D jeśli będzie takie pierwsze wyrażenie które polegnie to staramy się uzupełnić to z tego co już wiemy *)
let rec check_proof proofs premises conclusions sc proved = 
  let useNatualDeduction expr = useIntroductionRule premises conclusions expr || useEliminationRule premises conclusions expr  in
  let isProven expr = elem expr premises conclusions in 
  let condition expr = isProven expr || useNatualDeduction expr in

  match proofs with
  | Inset(premise, proof)::xs -> 
    check_proof proof (premise::premises) conclusions (fun expr -> check_proof xs premises (createImp premise expr ::conclusions) sc proved) proved
  | Expr(expr)::[] when isVar expr && PairMap.mem (getName expr) proved -> sc (PairMap.find (getName expr) proved)         
  | Expr(expr)::xs when isVar expr && PairMap.mem (getName expr) proved -> check_proof xs premises ((PairMap.find (getName expr) proved)::conclusions) sc proved    
  | Expr(expr)::[] when condition expr -> sc expr     
  | Expr(expr)::xs when condition expr -> check_proof xs premises (expr::conclusions) sc proved
  | Expr(expr)::_ -> 
    let pos = getPosition expr in 
    raise @@ IncorrectProof (Printf.sprintf "%s:%d:%d: Unexpected expression" pos.pos_fname pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1))
  | _ -> raise @@ IncorrectProof "This shouldnt happen"
;;

let run expr proof proved = 
  match expr with 
  | None -> check_proof proof [] [] (fun _ -> true) proved 
  | Some e -> check_proof proof [] [] (fun e' -> if equals e' e then true else raise @@ IncorrectProof "The expression hasn't been proved" ) proved 
;;