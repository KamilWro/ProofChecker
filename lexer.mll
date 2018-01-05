{
open Parser
open Lexing
open Datatypes

let next_line lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <-
    { pos with pos_bol = lexbuf.lex_curr_pos;
               pos_lnum = pos.pos_lnum + 1
    }
}

let digit = [ '0'-'9' ] 
let alpha = [ 'a'-'z' 'A' - 'Z' ]         
let white = [' ' '\t']+ 
let newline = '\r' | '\n' | "\r\n"
let var = alpha (alpha|digit|'_')* 

rule read = parse
  white                     { read lexbuf }
| newline                   { next_line lexbuf; read lexbuf }
| "goal"                    { GOAL }
| "proof"                   { PROOF }
| "end"                     { END }  
| "axiom"                   { AXIOM } 
| ";"                       { SEMICOLON }
| "["                       { LSQUARE }
| "]"                       { RSQUARE }
| "("                       { LPAREN }
| ")"                       { RPAREN }
| ":"                       { COLON }
| "\\/"                     { OR }
| "/\\"                     { AND}
| "=>"                      { IMP }
| "~"                       { NOT }
| "<=>"                     { EQ }
| "."                       { DOT }
| "T"                       { TRUE }
| "F"                       { FALSE }  
| var                       { VAR (lexeme lexbuf)}
| eof                       { EOF }
| _                         { raise @@ SyntaxError "Unexpected character" }