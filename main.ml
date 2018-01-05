module PairMap = Map.Make(StringMap)
open Lexing       
open Datatypes
open Lexer
open Proofchecker

let print_position outx lexbuf =
  let open Core.Std in 
  let pos = lexbuf.lex_curr_p in
  fprintf outx "%s:%d:%d" pos.pos_fname pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let run_with_error expr proof proved = 
  let open Core.Std in 
  try run expr proof proved with
  | Proofchecker.IncorrectProof msg ->
    fprintf stderr "%s \n" msg;
    false   

let parse_with_error lexbuf =
  let open Core.Std in 
  try Parser.prog Lexer.read lexbuf with
  | SyntaxError msg ->
    fprintf stderr "%a: %s\n" print_position lexbuf msg;
    Error
  | Parser.Error -> 
    fprintf stderr "%a: syntax error\n" print_position lexbuf;
    Error

let printInfo nameFile titleProof index msg =
  let open Core.Std in 
  fprintf stdout "%s :: %s Proof No. %d - %s " nameFile titleProof index msg      

let printWarn nameFile msg =
  let open Core.Std in 
  fprintf stdout "%s :: %s " nameFile msg      


let rec parse_and_print lexbuf index proved =
  match parse_with_error lexbuf with
  | EOF ->
    printWarn (lexbuf.lex_curr_p.pos_fname) "The end of the file! \n \n"
  | Error ->
    printWarn (lexbuf.lex_curr_p.pos_fname) "The program has been aborted because an error has occurred! \n"
  | Axiom (title, expr) ->
    printInfo (lexbuf.lex_curr_p.pos_fname) title index "Added a new axiom! \n"; 
    parse_and_print lexbuf (index + 1) (PairMap.add title expr proved) 
  | Goal (title, expr, proof) ->
    if run_with_error (Some expr) proof proved then 
      begin
        printInfo (lexbuf.lex_curr_p.pos_fname) title index "It is OK! \n";  
        parse_and_print lexbuf (index + 1) (PairMap.add title expr proved) 
      end          
    else
      begin
        (* printInfo (lexbuf.lex_curr_p.pos_fname) title index (Datatypes.show proof);   *)
        printInfo (lexbuf.lex_curr_p.pos_fname) title index "The proof is incorrect, read the error output! \n"; 
        parse_and_print lexbuf (index + 1) proved    
      end;
  | Proof proof ->
    if run_with_error None proof proved then 
      printInfo (lexbuf.lex_curr_p.pos_fname) "" index "It is OK! \n"
    else
      begin
        (* printInfo (lexbuf.lex_curr_p.pos_fname) "" index (Datatypes.show proof);   *)
        printInfo (lexbuf.lex_curr_p.pos_fname) "" index "The proof is incorrect, read the error output! \n"; 
      end;
    parse_and_print lexbuf (index + 1) proved

let main filename () =
  let open Core.Std in 
  print_string filename;
  let inx = In_channel.create filename in
  let lexbuf = Lexing.from_channel inx in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  let result = parse_and_print lexbuf 0 PairMap.empty in
  In_channel.close inx;
  result

(* let _ = main (Sys.argv.(1)) () *)

(* --------------------------------------------------------------------- tests --------------------------------------------------------------------- *)
let _ = main "tests/example.txt" () 
let _ = main "tests/incorrectProof.txt" () 
let _ = main "tests/modusPones.txt" () 
let _ = main "tests/myProofs.txt" () 
let _ = main "tests/pfW12.txt" () 
let _ = main "tests/proofChecker.txt" ()
let _ = main "tests/whiteBook.txt" () 