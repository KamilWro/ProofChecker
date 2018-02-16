{
open Parser
open Lexing
open DataTypes

let next_line lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <- { pos with pos_bol = lexbuf.lex_curr_pos; pos_lnum = pos.pos_lnum + 1 }
}

let digit = [ '0'-'9' ] 
let alpha = [ 'a'-'z' 'A' - 'Z' ]         
let white = [' ' '\t']+ 
let newline = '\r' | '\n' | "\r\n"
let var = [ 'a' - 'z' ] (alpha|digit|'_')*
let type = [ 'A' - 'Z' ] (alpha|digit|'_')* 
let comments = "(*" _* "*)"

rule read = parse
| "(*" 						{ read_comment lexbuf }
| white                     { read lexbuf }
| newline                   { next_line lexbuf; read lexbuf }
| "goal"                    { GOAL }
| "proof"                   { PROOF }
| "end"                     { END }  
| "axiom"                   { AXIOM } 
| "type"					{ TYPE }
| ","                       { COMMA }
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
| "<=>"                     { EQV }
| "."                       { DOT }
| "="                       { EQ }
| "T"                       { TRUE }
| "F"                       { FALSE }
| "V"                       { FORALL }
| "E"                       { EXISTS }
| type 						{ TYPE_NAME (lexeme lexbuf) }
| var                       { VAR (lexeme lexbuf) }
| eof                       { EOF }
| _                         { raise @@ Syntax_Error "Unexpected character" }

and read_comment = parse
| white                     { read_comment lexbuf }
| newline                   { next_line lexbuf; read_comment lexbuf }
| eof                       { EOF }
| "*)"						{ read lexbuf }
| _ 						{ read_comment lexbuf }