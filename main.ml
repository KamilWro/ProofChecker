open Lexing       
open DataTypes

let print_position outx pos =
  Core.Std.fprintf outx "%s:%d:%d" pos.pos_fname pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let run_with_error expr proof proved = 
  try 
    if Verification.run expr proof then ProofChecker.run proof proved else false
  with
  | ProofChecker.IncorrectProof(msg, pos) | Verification.SemanticError(msg, pos)  ->
    Core.Std.fprintf stderr "%a: %s\n" print_position pos msg;
    false   


let parse_with_error lexbuf = 
  try Parser.prog Lexer.read lexbuf with
  | SyntaxError msg ->
    Core.Std.fprintf stderr "%a: %s\n" print_position lexbuf.lex_curr_p msg;
    Error
  | Parser.Error -> 
    Core.Std.fprintf stderr "%a: syntax error\n" print_position lexbuf.lex_curr_p;
    Error

let print_info lexbuf titleProof index msg = 
  Core.Std.fprintf stdout "%s :: %s Proof No. %d - %s " (lexbuf.lex_curr_p.pos_fname) titleProof index msg      

let print_warn lexbuf msg = 
  Core.Std.fprintf stdout "%s :: %s " (lexbuf.lex_curr_p.pos_fname) msg      


let rec parse_and_print lexbuf index proved =
  match parse_with_error lexbuf with
  | EOF ->
    print_warn lexbuf "The end of the file! \n \n"
  | Error ->
    print_warn lexbuf "The program has been aborted because an error has occurred! \n"
  | Axiom (title, expr) ->
    print_info lexbuf title index ("Added a axiom "^title^"\n"); 
    parse_and_print lexbuf (index + 1) ((title, expr) :: proved) 
  | Goal (title, expr, proof) ->
    if run_with_error (Some expr) proof proved then 
      begin
        print_info lexbuf title index "It is OK! \n";  
        parse_and_print lexbuf (index + 1) ((title, expr) :: proved) 
      end          
    else
      begin
        print_info lexbuf title index (DataTypes.show proof);  
        print_info lexbuf title index "The proof is incorrect, read the error output! \n"; 
        parse_and_print lexbuf (index + 1) proved    
      end;
  | Proof proof ->
    if run_with_error None proof proved then 
      print_info lexbuf "" index "It is OK! \n"
    else
      begin
        print_info lexbuf "" index (DataTypes.show proof);  
        print_info lexbuf "" index "The proof is incorrect, read the error output! \n"; 
      end;
    parse_and_print lexbuf (index + 1) proved

let main filename () =
  let open Core.Std in 
  print_string filename;
  let inx = In_channel.create filename in
  let lexbuf = Lexing.from_channel inx in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  let result = parse_and_print lexbuf 0 [] in
  In_channel.close inx;
  result

(* let _ = main (Sys.argv.(1)) () *)

(* --------------------------------------------------------------------- tests --------------------------------------------------------------------- *)
let _ = main "tests/incorrectProof.txt" () 
let _ = main "tests/myProofs.txt" () 
let _ = main "tests/propositionalLogic.txt" ()
let _ = main "tests/predicateLogic.txt" ()
