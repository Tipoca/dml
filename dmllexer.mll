(*********************************************************************)
(*                                                                   *)
(*                         Dependent ML                              *)
(*                                                                   *)
(*                       (c) Hongwei Xi                              *)
(*                           July 2000                               *)
(*                                                                   *)
(*                     University of Cincinnati                      *)
(*                                                                   *)
(*                  Distributed by permission only.                  *)
(*                                                                   *)
(*********************************************************************)

(* dmllexer - The DML lexer. *)

{
open Dmlparser

exception Error of string

let char_for_backslash c =
  match c with
    'n' -> '\010'
  | 't' -> '\009'
  | 'b' -> '\008'
  | 'r' -> '\013'
  | c -> c

let char_for_decimal_code lexbuf i =
  let c = 100 * (Char.code(Lexing.lexeme_char lexbuf i) - 48) +
           10 * (Char.code(Lexing.lexeme_char lexbuf (i+1)) - 48) +
                (Char.code(Lexing.lexeme_char lexbuf (i+2)) - 48)
  in Char.chr (c land 0xff)

let linenum = ref 0
let comment_depth = ref 0
let keyword_table = Hashtbl.create 53
let _ =
  List.iter (fun (kwd, tok) -> Hashtbl.add keyword_table kwd tok)
  [ "and", AND;
    "as", AS;
    "bool", BOOL;
    "case", CASE;
    "datatype", DATATYPE;
    "else", ELSE;
    "end", END;
    "false", FALSE;
    "fn", FN;
    "fun", FUN;
    "if", IF;
    "in", IN;
    "int", INT;
    "let", LET;
    "nat", NAT;
    "of", OF;
    "op", OP;
    "sort", SORT;
    "then", THEN;
    "true", TRUE;
    "type", TYPE;
    "val", VAL;
    "with", WITH;
    "withtype", WITHTYPE
  ]

let process_id s = 
  try Hashtbl.find keyword_table s with Not_found -> IDENT s

let process_int s = CONSTINT (int_of_string s)
let process_float s = CONSTFLOAT (float_of_string s)
let process_newline () = linenum := 1 + !linenum

let string_buffer = ref (String.create 100) ;;
let string_size = ref 100;;
let string_pos = ref 0;;
let store_string_char char =
  begin
    if !string_pos >= !string_size then
      let str = String.create(2 * (!string_size))
      in
         begin
	   String.blit !string_buffer 0 str 0 !string_size;
	   string_buffer := str;
	   string_size := 2 * !string_size
	 end
    else ();
    String.set !string_buffer !string_pos char;
    string_pos := 1 + !string_pos
  end

let get_stored_string () = 
  let str = String.sub !string_buffer 0 !string_pos
  in (string_pos := 0; str)

}

let blank = [' ' '\t']
let newline = '\n'
let letter = ['a'-'z' 'A'-'Z']
let digit = ['0'-'9']
let symbolic = [
  '!' '%' '&' '$' '#' '+' '-' '/' ':' '<'
  '=' '>' '?' '@' '\\' '~' '`' '|' '*'
]
let letter_or_digit_or_prime_or_underscore =
  ['a'-'z' 'A'-'Z' '0'-'9' '\'' '_']
let int_literal = digit +
let float_literal =
  ['0'-'9']+ ('.' ['0'-'9']*)? (['e' 'E'] ['+' '-']? ['0'-'9']+)?

rule token = parse
  letter letter_or_digit_or_prime_or_underscore *
      { process_id (Lexing.lexeme lexbuf) }
| int_literal (* this must be placed ahead of the rule for float *)
      { process_int (Lexing.lexeme lexbuf) }
| float_literal
      { process_float (Lexing.lexeme lexbuf) }
| "(" { LPAREN }
| ")" { RPAREN }
| "{" { LBRACE }
| "}" { RBRACE }
| "[" { LBRACKET }
| "]" { RBRACKET }
| "~" { TILDE }
| "+" { PLUS }
| "-" { MINUS }
| "*" { TIMES }
| "/" { DIV }
| "%" { PERCENT }
| "->" { MINUSGT }
| "=>" { EQGT }
| "<-" { LTMINUS }
| "<>" { LTGT }
| "!=" { BANGEQ }
| "=" { EQ }
| ":" { COLON }
| ";" { SEMICOLON }
| "." { DOT }
| "," { COMMA }
| "<=" { LTEQ }
| ">=" { GTEQ }
| "<" { LT }
| ">" { GT }
| "&&" { AMPERAMPER }
| "||" { BARBAR }
| "&" { AMPER }
| "|" { BAR }
| "%" { PERCENT }
| "/\\" { LAND}
| "\\/" { LOR }
| "'" { QUOTE }
| "^" { CARET }
| "_" { UNDERSCORE }
| "::" { COLONCOLON }
| "@" { APPEND }
| blank + { token lexbuf }
| newline
      { process_newline (); token lexbuf }
| "(*" { comment_depth := 1; comment lexbuf }
| "\"" { string_pos := 0; string lexbuf; CONSTSTRING (get_stored_string ()) }
| "#\"" [^ '\\' '\''] "\""
      { CONSTCHAR (Lexing.lexeme_char lexbuf 1) }
| "#\"" '\\' ['\\' '\'' 'n' 't' 'b' 'r'] "\""
      { CONSTCHAR (char_for_backslash (Lexing.lexeme_char lexbuf 2)) }
| "#\"" '\\' digit digit digit "\""
      { CONSTCHAR (char_for_decimal_code lexbuf 2 ) }
| eof { EOF }
| _ { raise (Error "Token_error: illegal character") }

and string = parse
  "\"" { () }
| "\\" newline
       { process_newline (); string lexbuf }
| "\\\t" { string lexbuf }
| "\\\n" { string lexbuf }
| "\\t" { store_string_char '\t'; string lexbuf }
| "\\n" { store_string_char '\n'; string lexbuf }
| "\\\"" { store_string_char '\034'; string lexbuf }
| [' '-'~']
        {  store_string_char (Lexing.lexeme_char lexbuf 0); string lexbuf }
| eof { raise (Error "String_error: runaway string") }
| _ { raise (Error "String_error: illegal character") }

and comment = parse
  "(*" { comment_depth := 1 + !comment_depth; comment lexbuf }
| "*)" { comment_depth := !comment_depth - 1;
         if !comment_depth > 0 then comment lexbuf
         else token lexbuf }
| newline { process_newline (); comment lexbuf }
| eof { raise (Error "comment_error: runaway comment") }
| _ { comment lexbuf }

(* end of dmllexer.mll *)
