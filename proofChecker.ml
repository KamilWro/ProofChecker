module PairMap = Map.Make(String)
open DataTypes
open Lexing
open List

exception IncorrectProof of string * Lexing.position

let isReplacementFresh revar = function 
  | Fresh(var',expr,_) -> begin
      match getReplacementVar revar expr with 
      | None -> false
      | Some x -> x = var'
    end      
  | _ -> false  


(* ---------------------------------------------------- Reguły wprowadzenia ------------------------------------------------- *)

let impI expr exprs = exists (equals expr) exprs ;; 
let andI expr exprs = exists (equals @@ getExpr1 expr) exprs && exists (equals (getExpr2 expr)) exprs ;; 
let orlI expr exprs = exists (equals @@ getExpr1 expr) exprs ;;
let orrI expr exprs = exists (equals @@ getExpr2 expr) exprs ;;
let notI expr exprs = exists (equals @@ createImp (getExpr expr) @@ createFalse()) exprs ;; 
let eqI expr exprs = exists (equals @@ createImp (getExpr1 expr) (getExpr2 expr)) exprs && 
                     exists (equals @@ createImp (getExpr2 expr) (getExpr1 expr)) exprs ;;
let existsI x expr exprs = exists (fun e -> isReplacedVar x e && equals (removeVar x expr) (removeVar x e)) exprs ;;
let forallI x expr exprs = exists (fun e -> isReplacementFresh x e && equals (removeVar x (getExpr e)) (removeVar x expr) ) exprs ;;

let rec useIntroductionRule expr exprs = 
  match expr with 
  | Imp _ when impI expr exprs -> true 
  | And _ when andI expr exprs -> true 
  | Or _ when orlI expr exprs -> true 
  | Or _ when orrI expr exprs -> true 
  | Eq _ when eqI expr exprs -> true   
  | Not _ when notI expr exprs -> true  
  | True _ -> true
  | Exists (x,expr',_) when existsI x expr' exprs && isVar x expr' -> true 
  | Forall (x,expr',_) when forallI x expr' exprs && isVar x expr' -> true 
  | _ -> false
;;

(* ----------------------------------------------------- Reguły eliminacji -------------------------------------------------- *)

let doubleNotE expr exprs = exists (equals @@ createNot (createNot expr)) exprs ;;
let andlE expr exprs = exists (equals expr) (map getExpr1 (filter isAnd exprs)) ;;
let andrE expr exprs = exists (equals expr) (map getExpr2 (filter isAnd exprs)) ;;
let falseE expr exprs = exists (equals @@ createFalse()) exprs;;
let notE expr exprs = exists (fun x -> exists (equals @@ createNot x) exprs) (filter (fun x -> not(isNot x)) exprs) ;;

let impE expr exprs = 
  let impList = filter (fun x -> isImp x && equals (getExpr2 x) expr) exprs in
  let findExpr list = exists (fun x -> exists (equals x) exprs) list in
  findExpr (map getExpr1 impList)
;;

let orE expr exprs =
  let impList = filter (fun x -> isImp x && equals (getExpr2 x) expr) exprs in
  let getExprPairs list = flatten @@ mapi (fun i x -> mapi (fun j y -> (i,j,createOr (getExpr1 x) (getExpr1 y) )) list) list in
  let findOrExpr list = exists (fun (i,j,x) -> if i <> j then exists (equals x) (filter isOr exprs) else false) list in
  findOrExpr (getExprPairs impList)
;;

let eqlE expr exprs =  
  let eqList = filter (fun x -> isEq x && equals (getExpr2 x) expr) exprs in
  let findExpr list = exists (fun x -> exists (equals x) exprs) list in
  findExpr (map getExpr1 eqList) 
;;

let eqrE expr exprs =  
  let eqList = filter (fun x -> isEq x && equals (getExpr1 x) expr) exprs in
  let findExpr list = exists (fun x -> exists (equals x) exprs) list in
  findExpr (map getExpr2 eqList)
;;

let forallE expr exprs = exists (fun e -> isForall e && isReplacedVar (getVar e) expr && isVar (getVar e) e && equals (removeVar (getVar e) expr) (removeVar (getVar e) (getExpr e))) exprs ;;

(* brzydki zapis :P *)
let existsE expr exprs = 
  	let existsList = filter isExists exprs in
  	let impList = filter (fun e -> (isImp e) && equals (getExpr2 e) expr) exprs in
  	exists (fun ex ->  isVar (getVar ex) ex && exists (fun imp -> let expr = getExpr1 imp in isReplacementFresh (getVar ex) (getExpr1 imp) && equals (removeVar (getVar ex) @@ getExpr expr) (removeVar (getVar ex) (getExpr ex)) ) impList ) existsList 
;;


let rec useEliminationRule expr exprs =
  match expr with 
  | expr when andlE expr exprs -> true 
  | expr when andrE expr exprs -> true 
  | expr when impE expr exprs -> true 
  | expr when orE expr exprs -> true 
  | expr when falseE expr exprs -> true 
  | expr when notE expr exprs -> true
  | expr when doubleNotE expr exprs -> true
  | expr when forallE expr exprs -> true
  | expr when existsE expr exprs -> true
  | _ -> false
;;

(* -------------------------------------------------------- Dowodzenie ------------------------------------------------------ *)    
let getProof name proved pos =
  try assq name proved with
  | Not_found -> raise @@ IncorrectProof ("Incorrect reference", pos)

let rec deduceConclusions expr exprs proved sc = 
  match expr with
  | Ref (name,pos) -> sc @@ getProof name proved pos
  | expr when (exists (equals expr) exprs) || (useEliminationRule expr exprs) || (useIntroductionRule expr exprs) -> sc expr
  | _ -> print_string (List.fold_left (fun x y -> x ^ show_formula y ^ "; ") ">" exprs); print_newline; print_newline; raise @@ IncorrectProof ("It can not be proved", getPosition expr)

and checkProof proof exprs proved sc = 
  match proof with
  | Inset(assumption, proof, _)::xs -> 
    checkProof proof (assumption::exprs) proved (fun expr -> checkProof xs (createImp assumption expr :: exprs) proved sc)
  | FreshInset(fvar, None, proof, _)::xs -> 
    checkProof proof exprs proved (fun expr' -> checkProof xs ((createFresh fvar expr') :: exprs) proved sc)
  | FreshInset(fvar, Some assumption, proof, _)::xs ->
    checkProof xs (assumption::exprs) proved (fun expr' -> checkProof xs ((createImp (createFresh fvar assumption) expr') :: exprs) proved sc)
  | Expr(expr)::[] -> 
    deduceConclusions expr exprs proved sc      
  | Expr(expr)::xs -> 
    deduceConclusions expr exprs proved (fun e -> checkProof xs (e::exprs) proved sc)
;;

let run proof proved = checkProof proof [] proved (fun _ -> true) ;;
