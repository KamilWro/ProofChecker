%{
  open DataTypes
  open Lexing
  module PairMap = Map.Make(String)
%}

%token EOF
%token DOT SEMICOLON COLON LSQUARE RSQUARE LPAREN RPAREN COMMA RHOMB
%token OR AND IMP NOT EQ
%token PROOF END GOAL AXIOM REF
%token TRUE FALSE 
%token FORALL EXISTS
%token <string> VAR

%left EQ
%right IMP
%left OR
%left AND 
%right NOT

%start <Lexing.position DataTypes.typeCheckResult> prog

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
	| LSQUARE; premise = expression; COLON; nd = naturalDeduction; RSQUARE {Inset(premise, nd, $symbolstartpos)}
	| LSQUARE; LSQUARE; x = VAR; RSQUARE; COMMA; premise = expression; COLON; nd = naturalDeduction; RSQUARE {FreshInset(x, Some premise, nd, $symbolstartpos)}
	| LSQUARE; LSQUARE; x = VAR; RSQUARE; COLON; nd = naturalDeduction; RSQUARE {FreshInset(x, None, nd, $symbolstartpos)}
	| x = expression {Expr x}
	| {raise (SyntaxError "incorrect expression")} 
;

expression:
	| FORALL; x = VAR; DOT; e = expression {Forall(x,e,$symbolstartpos)}
	| EXISTS; x = VAR; DOT; e = expression {Exists(x,e,$symbolstartpos)}
	| REF; x = VAR; {Ref(x,$symbolstartpos)}
 	| f1 = expression; EQ; f2 = expression { Eq(f1, f2, $symbolstartpos) }
 	| f1 = expression; IMP; f2 = expression { Imp(f1, f2, $symbolstartpos) }
 	| f1 = expression; OR; f2 = expression { Or(f1, f2, $symbolstartpos) }
 	| f1 = expression; AND; f2 = expression { And(f1, f2, $symbolstartpos) }
 	| NOT; f = expression {Not (f,$symbolstartpos)}
 	| x = VAR; lists = vars { let xs,ys = lists in Atom (x, xs, ys, $symbolstartpos)}
 	| LPAREN; x = expression; RPAREN {x}
 	| TRUE { True($symbolstartpos) }
 	| FALSE { False($symbolstartpos) }
 	| {raise (SyntaxError "incorrect expression")} 
;

vars: 
	| { [],[] }
	| LPAREN; lists = revVars; RPAREN { lists }
;

revVars:
  | lists = revVars; COMMA; x = VAR { let xs,ys = lists in (x::xs,ys) }
  | lists = revVars; COMMA; x = VAR; RHOMB; y = VAR { let xs,ys = lists in (xs,(x,y)::ys) }
  | x = VAR; RHOMB; y = VAR { [],[x,y] }
  | x = VAR; {[x],[]}
;
