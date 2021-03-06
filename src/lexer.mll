{
  open Parser
}


let space = ' ' | '\t' | '\r'

rule token = parse
  | "coh" { COH }
  | "hyp" { HYP }
  | "check" { CHECK }
  | "let" { LET }
  | "eval" { EVAL }
  | "env" { ENV }
  | "in" {IN}
  | "(" { LPAR }
  | ")" { RPAR }
  | ":" { COL }
  | "->" { MOR }
  | "*" { OBJ }
  | "|" { PIPE }
  | "[" { LBRA }
  | "]" { RBRA }
  | "=" {EQUAL}
  | (['a'-'z''A'-'Z''0'-'9']['-''+''a'-'z''A'-'Z''0'-'9''_''@''{''}''/'',''\'']* as str) { IDENT str }
  | space+ { token lexbuf }
  | "#"[^'\n']* { token lexbuf }
  | '"'([^'"']* as str)'"' { STRING str }
  | "\n" { Lexing.new_line lexbuf; token lexbuf }
| eof { EOF }
