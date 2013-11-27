(********************************************************
   This file is part of coreStar
        src/parsing/lexer.mll
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   coreStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)

{

open Lexing
open Parser

type error =
  | Illegal_character of char
  | Unterminated_comment
  | Unterminated_literal

exception Error of error * Lexing.lexbuf

let nest_start_pos = ref []
let nest x = nest_start_pos := x.lex_curr_p :: !nest_start_pos
let unnest x = nest_start_pos := List.tl !nest_start_pos; !nest_start_pos <> []

let string_of_position p =
  let r = Buffer.create 10 in
  if p.pos_fname <> "" then begin
    Buffer.add_string r p.pos_fname; Buffer.add_char r ':'
  end;
  Printf.bprintf r "%d:%d" p.pos_lnum (p.pos_cnum - p.pos_bol);
  Buffer.contents r

let error_message e lb =
  match e with
    Illegal_character c ->
      Printf.sprintf "%s: illegal character: %s\n"
        (string_of_position lb.lex_curr_p) (Char.escaped c)
  | Unterminated_comment ->
      Printf.sprintf "%s: unterminated comment\n"
        (string_of_position (List.hd !nest_start_pos))
  | Unterminated_literal ->
      Printf.sprintf "%s: unterminated literal\n"
        (string_of_position (List.hd !nest_start_pos))

(* [kwd_or_else d s] is the token corresponding to [s] if there is one,
  or the default [d] otherwise. *)
let kwd_or_else =
  let keyword_table = Hashtbl.create 53 in
  List.iter (fun (kwd, tok) -> Hashtbl.add keyword_table kwd tok) [
    "emp", EMP;
    "false", FALSE;
    "assign", ASSIGN;
    "call", CALL;
    "end", END;
    "global", GLOBAL;
    "goto", GOTO;
    "if", IF;
    "import", IMPORT;
    "label", LABEL;
    "nop", NOP;
    "procedure", PROCEDURE;
    "rule", RULE;
  ];
  fun d s ->
  try Hashtbl.find keyword_table s with Not_found -> d

}


(* ====================================================================== *)

let  dec_digit = ['0' - '9']

let  not_cr_lf = [ ^ '\010' '\013']

let  alpha_char = ['a' - 'z'] | ['A' - 'Z']

let  simple_id_char = alpha_char | dec_digit | '_' | '.' | '$'

let  first_id_char = alpha_char | '_' | '$'

let  line_comment = "//" not_cr_lf*

let  blank = (' ' | '\009')+

let  ignored_helper = (blank | line_comment)+

let  newline = ('\013' | '\010' | "\010\013")

let  at_identifier =
      '@' (simple_id_char | ':')*

let identifier =
      first_id_char simple_id_char*

let integer = '0' | ['1'-'9'] ['0'-'9']*

rule token = parse
  | newline { Lexing.new_line lexbuf; token lexbuf }
  | "/*" { nest lexbuf; comment lexbuf; token lexbuf }
  | ignored_helper  { token lexbuf }
  | "!" { BANG }
  | "!=" { NOT_EQUALS }
  | "(" { L_PAREN }
  | ")" { R_PAREN }
  | "*" { MULT }
  | "+" { OP_PLUS }
  | "," { COMMA }
  | "-" { OP_MINUS }
  | "/" { OP_DIV }
  | ":" { COLON }
  | ":=" { COLON_EQUALS }
  | ";" { SEMICOLON }
  | "<" { CMP_LT }
  | "<=" { CMP_LE }
  | "=" { EQUALS }
  | ">" { CMP_GT }
  | ">=" { CMP_GE }
  | "?" { QUESTIONMARK }
  | "{" { L_BRACE }
  | "|-" { VDASH }
  | "||" { OROR }
  | "}" { R_BRACE }
  | eof { EOF }

  (* Both at_identifer and identifer should produce IDENTIFIER *)
  | at_identifier as s { kwd_or_else (IDENTIFIER s) s }
  | identifier as s { kwd_or_else (IDENTIFIER s) s }

  (* Lexing integers and strings according to SMT-LIB 2.0. *)
  | integer as s { INT_CONSTANT s }
  | '"' { nest lexbuf; STRING_CONSTANT (lex_string (Buffer.create 0) lexbuf) }

  | _ { failwith (error_message (Illegal_character ((Lexing.lexeme lexbuf).[0])) lexbuf)}
and comment = parse
  | "/*"  { nest lexbuf; comment lexbuf }
  | "*/"  { if unnest lexbuf then comment lexbuf }
  | newline  { Lexing.new_line lexbuf; comment lexbuf }
  | eof      { failwith (error_message Unterminated_comment lexbuf)}
  | _     { comment lexbuf; }
and lex_string b = parse
  | "\\\\" { Buffer.add_char b '\\'; lex_string b lexbuf }
  | "\\\"" { Buffer.add_char b '"'; lex_string b lexbuf }
  | '"' { let r = unnest lexbuf in assert (not r); Buffer.contents b }
  | eof { failwith (error_message Unterminated_literal lexbuf) }
  | _ as c { Buffer.add_char b c; lex_string b lexbuf }


(* ====================================================================== *)

{ (* trailer *)
}
