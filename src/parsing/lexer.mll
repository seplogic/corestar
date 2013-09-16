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

exception Error of error * Lexing.lexbuf

let nest_depth = ref 0
let nest_start_pos = ref dummy_pos
let nest x = incr nest_depth; nest_start_pos := x.lex_curr_p
let unnest x = decr nest_depth; !nest_depth <> 0

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
        (string_of_position !nest_start_pos)

(* [kwd_or_else d s] is the token corresponding to [s] if there is one,
  or the default [d] otherwise. *)
let kwd_or_else =
  let keyword_table = Hashtbl.create 53 in
  List.iter (fun (kwd, tok) -> Hashtbl.add keyword_table kwd tok) [
    "Abduction", ABDUCTION;
    "Emp", EMP;
    "False", FALSE;
    "Frame", FRAME;
    "Implication", IMPLICATION;
    "Inconsistency", INCONSISTENCY;
    "True", TRUE;
    "abstraction", ABSRULE;
    "assign", ASSIGN;
    "axioms", AXIOMS;
    "call", CALL;
    "constructor", CONSTRUCTOR;
    "end", END;
    "equiv", EQUIV;
    "global", GLOBAL;
    "goto", GOTO;
    "if", IF;
    "import", IMPORT;
    "label", LABEL;
    "nop", NOP;
    "notin", NOTIN;
    "notincontext", NOTINCONTEXT;
    "or", ORTEXT;
    "procedure", PROCEDURE;
    "pureguard", PUREGUARD;
    "rewrite", REWRITERULE;
    "rule", RULE;
    "where", WHERE;
    "with", WITH;
    "without", WITHOUT;
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

let  string_char = ['\000' - '\033'] | ['\035' - '\091'] | ['\093' - '\127']

let  line_comment = "//" not_cr_lf*

let  blank = (' ' | '\009')+

let  ignored_helper = (blank | line_comment)+

let  newline = ('\013' | '\010' | "\010\013")

let  at_identifier =
      '@' (simple_id_char | ':')*

let identifier =
      first_id_char simple_id_char*

rule token = parse
  | newline { Lexing.new_line lexbuf; token lexbuf }
  | "/*" { nest lexbuf; comment lexbuf; token lexbuf }
  | ignored_helper  { token lexbuf }
  | "," { COMMA }
  | "{" { L_BRACE }
  | "}" { R_BRACE }
  | ";" { SEMICOLON }
  | "[" { L_BRACKET }
  | "]" { R_BRACKET }
  | "(" { L_PAREN }
  | ")" { R_PAREN }
  | ":" { COLON }
  | "." { DOT }
  | "'" { QUOTE }
  | ":=" { COLON_EQUALS }
  | "=" { EQUALS }
  | "&" { AND }
  | "|" { OR }
  | "||" { OROR }
  | "!=" { NOT_EQUALS }
  | "*" { MULT }
  | "-*" { WAND }
  | "=>" { IMP }
  | "<=>" { BIMP }
  | "?" { QUESTIONMARK }
  | "!" { BANG }
  | "|-" { VDASH }
  | "~~>" { LEADSTO }
  | "/" { OP_DIV }
  | "-" { OP_MINUS }
  | "+" { OP_PLUS }
  | "<=" { CMP_LE }
  | "<" { CMP_LT }
  | ">=" { CMP_GE }
  | ">" { CMP_GT }
  | eof { EOF }

  (* Both at_identifer and identifer should produce IDENTIFIER *)
  | at_identifier as s { kwd_or_else (IDENTIFIER s) s }
  | identifier as s { kwd_or_else (IDENTIFIER s) s }

  (* FIXME: What is the right lexing of string constants? *)
  | '"' (string_char* as s) '"' { STRING_CONSTANT s }
  | _ { Printf.printf "here2 %!"; failwith (error_message (Illegal_character ((Lexing.lexeme lexbuf).[0])) lexbuf)}
and comment = parse
  | "/*"  { nest lexbuf; comment lexbuf }
  | "*/"  { if unnest lexbuf then comment lexbuf }
  | newline  { Lexing.new_line lexbuf; comment lexbuf }
  | eof      { failwith (error_message Unterminated_comment lexbuf)}
  | _     { comment lexbuf; }


(* ====================================================================== *)

{ (* trailer *)
}
