(********************************************************
   This file is part of coreStar
        src/prover/congruence.mli
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   coreStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)

open Corestar_std

module type PCC =
  sig
    type t
    type constant
    type term = TConstant of constant | Func of constant * term list
    type curry_term = Constant of constant | App of curry_term * curry_term
    type pattern =
        Hole of constant
      | PConstant of constant
      | PFunc of constant * pattern list
    val create : unit -> t
    val size : t -> int
    val add_term : t -> term -> constant * t
    val add_app : t -> constant -> constant -> constant * t
    val fresh : t -> constant * t
    val fresh_unifiable : t -> constant * t
    val fresh_exists : t -> constant * t
    val fresh_unifiable_exists : t -> constant * t
    val merge_cc : (constant -> bool * constant) -> t -> t -> t
    val make_equal : t -> constant -> constant -> t
    val rep_eq : t -> constant -> constant -> bool
    val rep_uneq : t -> constant -> constant -> bool
    val rep_not_used_in : t -> constant -> constant list -> bool
    val rep_self_cons : t -> constant -> bool
    val make_not_equal : t -> constant -> constant -> t
    val make_constructor : t -> constant -> t
    val normalise : t -> constant -> constant
    val others : t -> constant -> constant list
    val eq_term : t -> curry_term -> curry_term -> bool
    val neq_term : t -> curry_term -> curry_term -> bool
    val unifies : t -> curry_term -> constant -> (t -> 'a) -> 'a
    val unifies_any : t -> curry_term -> (t * constant -> 'a) -> 'a
    val determined_exists :
      t -> (constant list) -> constant -> constant -> t * (constant * constant) list
    val compress_full : t -> t * (constant -> constant)
    val print : t -> unit
    val pretty_print :
      (constant -> bool) ->
      (Format.formatter -> constant -> unit) -> Format.formatter -> t -> unit
    val pretty_print' :
      (constant -> bool) ->
      (Format.formatter -> constant -> unit) ->
      Printing.sep_wrapper -> Format.formatter -> bool -> t -> bool
    val pp_c : t -> constant pretty_printer
    val get_eqs :
      (constant -> bool) -> (constant -> 'a) -> t -> ('a * 'a) list
    val get_neqs :
      (constant -> bool) -> (constant -> 'a) -> t -> ('a * 'a) list
      
    val get_consts : t -> constant list
    val get_reps : (constant -> bool) -> (constant -> 'a) -> t -> 'a list 
    val get_self_constructors : t -> constant list

    (* surjective mapping from constants to integers *)
    val const_int : constant -> t -> int 
  
    val test : unit -> unit
    val delete : t -> constant -> t

    val forget_qs : t -> t

    val invariant : t -> bool
  end
module CC : PCC
