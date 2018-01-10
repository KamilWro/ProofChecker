open DataTypes

exception SemanticError of string * Lexing.position

let rec verification proof fvars sc = 
  match proof with
  | Inset(assumption, proof,_)::xs -> 
    verification proof fvars (fun expr -> verification xs fvars sc)
  | FreshInset(fvar, _, _, pos)::_ when List.mem fvar fvars -> 
    raise @@ SemanticError ("Expected fresh variables", pos) 
  | FreshInset(fvar, Some assumption, _, pos)::_ when not(isReplacementVar fvar assumption) -> 
    raise @@ SemanticError ("The assumption should contain a fresh variable", pos)
  | FreshInset(fvar, None, proof, _)::xs -> begin
      let sc' expr' =  
        if isReplacementVar fvar expr' then 
          verification xs (fvar::fvars) sc 
        else 
          raise @@ SemanticError ("The expression should contain a variable: " ^ fvar, getPosition expr') 
      in   
      verification proof fvars sc' 
    end
  | FreshInset(fvar, Some assumption, proof, _)::xs ->
    verification xs fvars sc
  | Expr(expr)::[] -> 
    sc expr     
  | Expr(expr)::xs -> 
    verification xs fvars sc
  | Inset(_, _, p)::_ | FreshInset(_, _, _, p)::_ -> raise @@ SemanticError ("Expected proof of the expression", p)

let run expr proof = 
  match expr with 
  | None -> verification proof [] (fun _ -> true)  
  | Some e -> verification proof [] (fun e' -> if equals e' e then true else raise @@ SemanticError ("Expected proof of the expression",getPosition e') ) 

