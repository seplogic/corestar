(********************************************************
   This file is part of coreStar
        src/utils/printing.ml
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   coreStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)


open Format

(* TODO(rgrig): Shouldn't this keep track of the file path too? *)
(* TODO(rgrig): Should probably be in a different file. *)
type source_location =
  { begin_line : int
  ; begin_column : int
  ; end_line : int
  ; end_column : int }

let unknown_location =
  { begin_line = -1; begin_column = -1; end_line = -1; end_column = -1}


(** Maps node identifiers (as used in symbolic execution) to locations. *)
(* TODO(rgrig): I think [int] should be [node_id] or similar. *)
let locations : (int, source_location) Hashtbl.t = 
  Hashtbl.create 101

(*DBG
  let dump_locations () = 
    printf "@[<2>Locations table:";
    Hashtbl.iter 
      (fun k, {bl=begin_line;bc=begin_column;el=end_line;ec=end_column} -> 
        printf "@\n%d -> %d:%d-%d:%d" k bl bc el ec)
      locations;
    printf "@."
*)

let add_location i = function
  | None -> ()
  | Some l -> Hashtbl.add locations i l

let find_location i =
  try Hashtbl.find locations i with Not_found -> unknown_location

let pp_json_location l t c =
  printf "@\njson {\"error_pos\": {";
  List.iter (fun (k, v) -> printf "\"%s\": \"%d\"," k v) [
    ("sline", l.begin_line);
    ("eline", l.end_line);
    ("spos", l.begin_column);
    ("epos", l.end_column)];
  printf "},\"error_text\": \"%s\",\"counter_example\": \"%s\"}@\n" (String.escaped t) (String.escaped c)

let pp_json_location_opt = function
  | None -> pp_json_location unknown_location
  | Some l -> pp_json_location l

let pp_json_node i = pp_json_location (find_location i)

(* {{{ pretty printing of collections
 * See 
 *   http://rgrig.blogspot.com/2010/09/certain-type-of-pretty-printing-in.html
 * for a little background. *)

type sep_wrapper = {
  separator : 'a. (formatter -> 'a -> unit) -> formatter -> bool -> 'a -> bool
}
let pp_sep sep_text = {
  separator = fun pp ppf first x ->
    if not first then fprintf ppf "@, %s " sep_text; pp ppf x; false
}
let pp_star = pp_sep "*"

let pp_whole pp_element pp_separator =
  fun ppf x -> ignore (pp_element pp_separator ppf true x)

(* {{{ printing for typical collection elements *)
let pp_paren pp f = fprintf f "(%a)" pp
let pp_binary_op operator pp_operand f (l, r) =
  fprintf f "@[@[%a@]%s@[%a@]@]@," pp_operand l operator pp_operand r
let pp_eq pp_operand = pp_binary_op "=" pp_operand
let pp_neq pp_operand = pp_binary_op "!=" pp_operand
let pp_disjunct pp_operand = pp_paren (pp_binary_op " || " pp_operand)
(* }}} *)
(* }}} *)
