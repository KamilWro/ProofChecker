open DataTypes
open Expression
open Lexing
open List

exception Incorrect_Proof of string * Lexing.position

let rec deduce_conclusions expr exprs fexprs proved types = 
  exists (equal expr) exprs ||
  EliminationRules.use expr exprs || 
  IntroductionRules.use expr exprs ||
  PredicateLogicRules.use expr exprs fexprs types ||
  exists (fun e' -> eq expr e' types) proved


and check_proof proof exprs fexprs proved types sc = 
  match proof with
  | Inset(assumption, proof, _)::xs -> 
    let exprs' e' = Imp(assumption, e') :: exprs in
    check_proof proof (assumption::exprs) fexprs proved types (fun e' -> check_proof xs (exprs' e') fexprs proved types sc)
  | Fresh_Inset(vtype, None, proof, _)::xs ->
    let types' = vtype::types in 
    let fexprs' e'= (vtype, e') :: fexprs in
    check_proof proof exprs fexprs proved types' (fun e' -> check_proof xs exprs (fexprs' e') proved types' sc)
  | Fresh_Inset(vtype, Some assumption, proof, _)::xs ->
    let types' = vtype :: types in 
    let fexprs' e' = (vtype, Imp(assumption, e')) :: fexprs in
    check_proof proof (assumption::exprs) fexprs proved types' (fun e' -> check_proof xs exprs (fexprs' e') proved types' sc)        
  | Expr(expr, pos)::xs -> 
    if deduce_conclusions expr exprs fexprs proved types then
      if xs = [] then sc expr else check_proof xs (expr::exprs) fexprs proved types sc
    else
      raise @@ Incorrect_Proof ("It can not be proved", pos)

let run proof proved types = 
  check_proof proof [] [] proved types (fun _ -> true) 
