%{
  open Datatypes
  open Lexing
%}

%token EOF
%token DOT SEMICOLON COLON LSQUARE RSQUARE LPAREN RPAREN
%token OR AND IMP NOT EQ
%token PROOF END GOAL AXIOM
%token TRUE FALSE
%token <string> VAR

%left EQ
%right IMP
%left OR
%left AND 
%right NOT

%start <Lexing.position Datatypes.typeCheckResult> prog

%%

prog:
  | EOF       { EOF }
  | v = definition { v } 
; 

definition:
	| GOAL; title = VAR; COLON; expr = expression; PROOF; nd = naturalDeduction; END; DOT { Goal(title, expr, nd) } 
	| PROOF; nd = naturalDeduction; END; DOT {Proof nd}
	| AXIOM; title = VAR; COLON; expr = expression; DOT {Axiom (title,expr)}
	| {raise (SyntaxError "incorrect definition")} 
;

naturalDeduction: 
	| list = revNaturalDeduction { List.rev list }
	| {raise (SyntaxError "incorrect proof")} 
;

revNaturalDeduction:
  | { [] }
  | xs = revNaturalDeduction; SEMICOLON; x = proof { x :: xs }
  | x = proof { [x] }
;

proof:
	| LSQUARE; premise = expression; COLON; nd = naturalDeduction; RSQUARE {Inset(premise,nd)}
	| x = expression {Expr x}
	| {raise (SyntaxError "incorrect expression")} 
;

expression:
 	| f1 = expression; EQ; f2 = expression { Eq(f1, f2, $symbolstartpos) }
 	| f1 = expression; IMP; f2 = expression { Imp(f1, f2, $symbolstartpos) }
 	| f1 = expression; OR; f2 = expression { Or(f1, f2, $symbolstartpos) }
 	| f1 = expression; AND; f2 = expression { And(f1, f2, $symbolstartpos) }
 	| NOT; f = expression {Not (f,$symbolstartpos)}
 	| LPAREN; v = expression; RPAREN {v}
 	| x = VAR { Var (x, $symbolstartpos )}
 	| TRUE { True($symbolstartpos) }
 	| FALSE { False($symbolstartpos) }
 	| {raise (SyntaxError "incorrect expression")} 
;
