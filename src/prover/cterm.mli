(********************************************************
   This file is part of coreStar
        src/prover/cterm.mli
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   coreStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)

open Corestar_std
open Format

type term_structure

type term_handle

type pattern

(*
   Create a new term structure
   It is externally functional, however underneath it uses mutation,
   so best to create new ones, rather than having a single starting one.
*)
val new_ts : unit -> term_structure

val conjoin : term_structure -> term_structure -> term_structure

(* Convert a Psyntax.args with AnyVars into a pattern to match *)
(*val make_pattern : Psyntax.args -> term_structure -> (pattern * term_structure)))))))))*)

val unifies : term_structure -> pattern -> term_handle -> (term_structure -> 'a) -> 'a

val determined_exists : term_structure -> (term_handle list) -> term_handle -> term_handle -> term_structure  * (term_handle * term_handle) list


(* Match pattern against the term_handle in the current term structure,
   the new term structure (with the unified variables) will be passed to the continuation
   Will raise No_match if no match can be found.
   Continutation can cause back tracking of pattern match by raising No_match
*)
(*val match_pattern : term_structure -> pattern -> term_handle -> (term_structure -> 'a) -> 'a*)

(*
   Add Psyntax to the term_structure, and return a term_handle and updated term structure
*)

val ground_pattern_tuple : Psyntax.args list -> term_structure -> (term_handle * term_structure)

val ground_pattern : Psyntax.args -> term_structure -> (term_handle * term_structure)

val add_term : bool -> Psyntax.args -> term_structure -> (term_handle * term_structure)

val add_pattern : Psyntax.args -> term_structure -> (pattern * term_structure)

val equal : term_structure -> term_handle -> term_handle -> bool

val unify_patterns : term_structure -> pattern -> pattern -> (term_structure -> 'a) -> 'a

val not_equal : term_structure -> term_handle -> term_handle -> bool

val unify_not_equal_pattern : term_structure -> pattern -> pattern -> (term_structure -> 'a) -> 'a

val make_equal : term_structure -> term_handle -> term_handle -> term_structure

val make_list_equal  : term_structure -> term_handle list -> term_structure

val normalise : term_structure -> term_handle -> term_handle

(*
   Return a compressed term_structure, will remove redundant terms.
*)
val compress : term_structure -> term_structure * (term_handle -> term_handle)

val make_not_equal : term_structure -> term_handle -> term_handle -> term_structure

val add_tuple : bool -> Psyntax.args list -> term_structure -> term_handle * term_structure

val make_tuple_pattern : Psyntax.args list -> term_structure -> pattern * term_structure


val make_equal_t : bool -> term_structure -> Psyntax.args -> Psyntax.args -> term_structure
val make_not_equal_t : bool -> term_structure -> Psyntax.args -> Psyntax.args -> term_structure

val blank_pattern_vars : term_structure -> term_structure

val pp_ts : term_structure pretty_printer
val pp_ts' : Printing.sep_wrapper -> formatter -> bool -> term_structure -> bool

val get_pargs : bool -> term_structure -> term_handle list -> term_handle -> Psyntax.args
val get_pargs_norecs : bool -> term_structure -> term_handle list -> term_handle -> Psyntax.args

val pp_c : term_structure -> formatter -> term_handle -> unit
val has_pp_c : term_structure -> term_handle -> bool

val get_args_rep : term_structure -> (term_handle * Psyntax.args) list
val get_args_all : term_structure -> Psyntax.args list

val get_eqs : term_structure -> (Psyntax.args * Psyntax.args) list
val get_neqs : term_structure -> (Psyntax.args * Psyntax.args) list

(* TODO: temporary until the bug in has_pp_c gets resolved *)
val get_eqs_all : term_structure -> (Psyntax.args * Psyntax.args) list
val get_neqs_all : term_structure -> (Psyntax.args * Psyntax.args) list

val get_eqs_norecs : term_structure -> (Psyntax.args * Psyntax.args) list
val get_neqs_norecs : term_structure -> (Psyntax.args * Psyntax.args) list

exception Var_not_found
val freshen_exists : Vars.var * term_structure -> Vars.var * term_structure
  (* [freshen_exists (v, ts)] throws [Var_not_found] if [v] is not in [ts] *)
val get_term : term_structure -> term_handle-> Psyntax.args
val kill_var : term_structure -> Vars.var -> term_structure
val update_var_to : term_structure -> Vars.var -> Psyntax.args -> term_structure

val rewrite : term_structure -> Psyntax.rewrite_rule list -> (term_structure * Psyntax.rewrite_guard -> bool) -> term_structure

val ts_eq : term_structure -> term_structure -> bool

val var_not_used_in : term_structure -> Vars.var -> term_handle list -> bool
val var_not_used_in_term : term_structure -> Vars.var -> Psyntax.args -> bool

val add_constructor : string -> term_structure -> term_structure
val import_constructors : term_structure -> term_structure -> term_structure

val get_equals_pvar_free : term_structure -> Vars.var -> Psyntax.args list
val get_pvars : term_structure -> Vars.var list

val forget_internal_qs : term_structure -> term_structure
