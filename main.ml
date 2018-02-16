open Lexing       
open DataTypes

let print_position outx pos =
  Core.Std.fprintf outx "%s:%d:%d" pos.pos_fname pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let type_check_with_error lexbuf expr proof =
  try Verification.run expr proof with
  | Verification.Incorrect_Proof(msg, pos)  ->
    Core.Std.fprintf stderr "%a: %s\n" print_position pos msg;
    false   
  | Verification.No_Proof msg->
    Core.Std.fprintf stderr "%a: %s\n" print_position lexbuf.lex_curr_p msg;
    false  

let eval_with_error proof proved types = 
  try ProofChecker.run proof proved types with
  | ProofChecker.Incorrect_Proof(msg, pos) -> 
    Core.Std.fprintf stderr "%a: %s\n" print_position pos msg;
    false   

let parse_with_error lexbuf = 
  try Parser.prog Lexer.read lexbuf with
  | Syntax_Error msg ->
    Core.Std.fprintf stderr "%a: %s\n" print_position lexbuf.lex_curr_p msg;
    Error
  | Parser.Error -> 
    Core.Std.fprintf stderr "%a: syntax error\n" print_position lexbuf.lex_curr_p;
    Error

let print_info lexbuf titleProof index msg = 
  Core.Std.fprintf stdout "%s :: %s Proof No. %d - %s " (lexbuf.lex_curr_p.pos_fname) titleProof index msg      

let print_warn lexbuf msg = 
  Core.Std.fprintf stdout "%s :: %s " (lexbuf.lex_curr_p.pos_fname) msg      

let rec parse_and_print lexbuf index proved types =
  match parse_with_error lexbuf with
  | EOF ->
    print_warn lexbuf "The end of the file! \n \n"
  | Error ->
    print_warn lexbuf "The program has been aborted because an error has occurred! \n \n"
  | Axiom expr -> 
    print_info lexbuf "" index ("Added axiom \n"); 
    parse_and_print lexbuf (index + 1) (expr :: proved) types
  | Goal (title, expr, proof) ->
    if type_check_with_error lexbuf (Some expr) proof && eval_with_error proof proved types then
      begin
        print_info lexbuf title index "It is OK! \n";  
        parse_and_print lexbuf (index + 1) (expr :: proved) types 
      end          
    else
      begin
        print_info lexbuf title index "The proof is incorrect, read the error output! \n"; 
        parse_and_print lexbuf (index + 1) proved types    
      end;
  | Proof proof ->
    if type_check_with_error lexbuf None proof && eval_with_error proof proved types then
      print_info lexbuf "" index "It is OK! \n"
    else
      print_info lexbuf "" index "The proof is incorrect, read the error output! \n"; 
    parse_and_print lexbuf (index + 1) proved types
  | Type (v, t) -> 
    print_info lexbuf "" index "Added new type! \n";
    parse_and_print lexbuf (index + 1) proved ((v,Some t)::types)

let main filename () =
  let open Core.Std in 
  print_string filename;
  let inx = In_channel.create filename in
  let lexbuf = Lexing.from_channel inx in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  let result = parse_and_print lexbuf 0 [] [] in
  In_channel.close inx;
  result

let _ = main (Sys.argv.(1)) () 

(* (* --------------------------------------------------------------------- tests --------------------------------------------------------------------- *)
   let _ = main "tests/incorrectProof.txt" () 
   let _ = main "tests/axiom.txt" () 
   let _ = main "tests/propositionalLogic.txt" ()
   let _ = main "tests/predicateLogic.txt" ()
*)