{
    open Bobgram
    open Lexing
    let next_line lexbuf =
      let pos = lexbuf.lex_curr_p in
      lexbuf.lex_curr_p <-
        { pos with pos_bol = lexbuf.lex_curr_pos;
                   pos_lnum = pos.pos_lnum + 1
        }
}
let white = [' ' '\t']+
let stext = ['a'-'z' '_']['a'-'z' '_' '0'-'9' '\'']*
let ctext = ['A'-'Z']['A'-'Z' '_' '0'-'9' '\'']*

rule read = parse
| white { read lexbuf }
| '\n' { next_line lexbuf; read lexbuf }
| "(*" { comment lexbuf }
| "Type" { TYPE }
| "Declare" { DECLARE }
| "Typemacro" { TYPEMACRO }
| "Macro" { MACRO }
| "Check" { CHECK }
| "Eval" { EVAL }
| "->" { ARROW }
| '+' { PLUS }
| '1' { ONE }
| "()" { UNIT }
| '.' { POINT }
| '=' { EQUAL }
| '(' { LEFT_PAREN }
| ')' { RIGHT_PAREN }
| ',' { COMMA }
| '[' { LEFT_BRACKET }
| ']' { RIGHT_BRACKET }
| "left" { LEFT }
| "right" { RIGHT }
| "fold" { FOLD }
| "rec" { REC }
| "fun" { FUN }
| ':' { COLON }
| "comp" { COMP }
| "letr" { LETR }
| "in" { IN }
| "unfold" { UNFOLD }
| "case" { CASE }
| "of" { OF }
| "ret" { RET }
| '*' { STAR }
| "lets" { LETS }
| stext { ID (Lexing.lexeme lexbuf) }
| ctext { MID (Lexing.lexeme lexbuf) }
| eof { EOF }
| _ { raise (Utils.SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }

and comment = parse
| "*)" { read lexbuf }
| '*' { comment lexbuf }
| [^ '*']+ { comment lexbuf }
