# ProofChecker
Program do sprawdzenia poprawności dowodów formuł logicznych w systemie dedukcji naturalnej.

## Wprowadzone rozszerzenia:
- [x] Obsługa formuł I rzędu
- [x] Możliwość korzystania z aksjomatów
- [x] Możliwość korzystania z udowodnionych formuł
- [x] Obsługa arytmentyki pierwszego rzędu
- [x] Informacja o lokalizacji i rodzaju błędu 
- [ ] Automatycznie wypełnianie dziur
- [ ] Generowanie drzew dowodu za pomocą termów rachunku lambda

Więcej informacji w [dokumentacji](/documentation/projekt-pc.pdf) programu oraz w [instrukcji](/documentation/instrukcja.pdf) obsługi aplikacji.

## Kompilacja:

`ocamlbuild -I rules -use-menhir -tag thread -use-ocamlfind -quiet -pkg core main.native`

## Testowanie:
`./main.native test.txt` lub `./main.native test.txt >> log_file 2>> err_file`

## Gramatyka:
- program -> definition | definition_program
- definition -> <br/>
  | `goal` label `:` expression `proof` natural_deduction `end.` <br/>
  | `proof` natural deduction `end.`<br/>
  | `axiom` expression`.` <br/>
  | `type` label `( ) =` type_name`.`  <br/>  
- natural deduction -> <br/>
  | natural_deduction `;` proof <br/>
  | proof <br/>
- proof -> <br/>
  | `[` premise `:` natural deduction `]` <br/>
  | `[ [` var `] ,` expression `:` natural deduction `]` <br/>
  | `[ [` var`:` type_name`],` premise`:` natural_deduction `]`<br/>
  | `[ [` var`:` type_name`]:` natural_deduction `]` <br/> 
  | `[ [` var `] :`  natural_deduction `]` <br/> 
  | expression <br/>
- premise -> expression<br/>  
- expression -> <br/> 
  | term `=` term <br/> 
  | expression `<=>` expression <br/> 
  | expression `=>` expression<br/> 
  | expression `\/` expression<br/> 
  | expression `/\` expression<br/> 
  | `~` expression<br/> 
  | var `(`term`)`<br/> 
  | var<br/> 
  | `(`expression`)`<br/> 
  | `T`<br/> 
  | `F`<br/> 
  | `V` var`.` expression<br/> 
  | `V` var `:` type_name `.` expression<br/> 
  | `E` var`.` expression<br/> 
  | `E` var `:` type_name `.` expression<br/> 
- term ->  term`,`var  | var<br/>  

> var - dowolnej długości ciąg znaków zaczynający się od małej litery <br/> 
> type_name - dowolnej długości ciąg znaków zaczynający się od dużej litery<br/> 
> V - Kwantyfikator ogólny<br/> 
> E - Kwantyfikator egzystencjalny<br/> 

