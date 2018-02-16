%{
  open DataTypes
  open Lexing
%}

%token EOF
%token DOT SEMICOLON COLON LSQUARE RSQUARE LPAREN RPAREN COMMA
%token OR AND IMP NOT EQV EQ
%token PROOF END GOAL AXIOM TYPE
%token TRUE FALSE 
%token FORALL EXISTS
%token <string> VAR
%token <string> TYPE_NAME

%left EQV
%right IMP
%left OR
%left AND 
%left EQ
%nonassoc NOT
%nonassoc UEXISTS
%nonassoc UFORALL

%start <Lexing.position DataTypes.type_check_result> prog

%%

prog:
  | EOF { EOF }
  | v = definition { v } 
; 

definition:
  | GOAL; id = VAR; COLON; expr = expression; PROOF; nd = natural_deduction; END; DOT { Goal(id, expr, nd) } 
  | PROOF; nd = natural_deduction; END; DOT { Proof nd }
  | AXIOM; expr = expression; DOT { Axiom expr }
  | TYPE; id = VAR; LPAREN; RPAREN; EQ; t = TYPE_NAME; DOT { Type(id, t) }
  | { raise (Syntax_Error "incorrect definition") } 
;

natural_deduction: 
  | list = rev_natural_deduction { List.rev list }
;

rev_natural_deduction:
  | { [] }
  | xs = rev_natural_deduction; SEMICOLON; x = proof { x :: xs }
  | x = proof { [x] }
;

proof:
  | LSQUARE; premise = expression; COLON; nd = natural_deduction; RSQUARE { Inset(premise, nd, $symbolstartpos) }
  | LSQUARE; LSQUARE; x = VAR; RSQUARE; COMMA; premise = expression; COLON; nd = natural_deduction; RSQUARE { Fresh_Inset((x, None), Some premise, nd, $symbolstartpos) }
  | LSQUARE; LSQUARE; x = VAR; COLON; t = TYPE_NAME; RSQUARE; COMMA; premise = expression; COLON; nd = natural_deduction; RSQUARE { Fresh_Inset((x, Some t), Some premise, nd, $symbolstartpos) }
  | LSQUARE; LSQUARE; x = VAR; COLON; t = TYPE_NAME; RSQUARE; COLON; nd = natural_deduction; RSQUARE { Fresh_Inset((x, Some t), None, nd, $symbolstartpos) }
  | LSQUARE; LSQUARE; x = VAR; RSQUARE; COLON; nd = natural_deduction; RSQUARE { Fresh_Inset((x, None), None, nd, $symbolstartpos) }
  | x = expression { Expr (x, $symbolstartpos) }
  | { raise (Syntax_Error "incorrect expression") } 
;

expression:
  | t1 = term; EQ; t2 = term { Eq(t1, t2) }
  | e1 = expression; EQV; e2 = expression { Eqv(e1, e2) }
  | e1 = expression; IMP; e2 = expression { Imp(e1, e2) }
  | e1 = expression; OR; e2 = expression { Or(e1, e2) }
  | e1 = expression; AND; e2 = expression { And(e1, e2) }
  | NOT; e = expression { Not (e) }
  | id = VAR; xs = terms { Atom (id, xs) }
  | id = VAR { Atom (id, [])  }
  | LPAREN; x = expression; RPAREN { x }
  | TRUE { True }
  | FALSE { False }
  | FORALL; x = VAR; DOT; e = expression %prec UFORALL { Forall((x, None), e) }
  | FORALL; x = VAR; COLON; t = TYPE_NAME; DOT; e = expression %prec UFORALL { Forall((x, Some(t)), e) }
  | EXISTS; x = VAR; DOT; e = expression %prec UEXISTS { Exists((x, None), e) }
  | EXISTS; x = VAR; COLON; t = TYPE_NAME; DOT; e = expression %prec UEXISTS { Exists((x, Some(t)), e) }
  | { raise (Syntax_Error "incorrect expression") } 
;

term:
  | id = VAR; xs = terms { Function(id, xs) }
  | var = VAR; { Var var }
  | { raise (Syntax_Error "incorrect term") } 
;  

terms:
  | LPAREN; RPAREN; { [] }
  | LPAREN; list = rev_terms; RPAREN { list }
;

rev_terms:
  | xs = rev_terms; COMMA; x = term { x :: xs }
  | x = term { [x] }
;