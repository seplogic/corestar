(********************************************************
   This file is part of coreStar
        src/symbexe/symexec.mli
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   coreStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)


type ntype = Plain | Good | Error | Abs | UnExplored
type etype = ExecE | AbsE | ContE | ExitE
type id = int
val file : string ref
val set_group : bool -> unit
type node = {
  mutable content : string;
  id : id;
  mutable ntype : ntype;
  mutable url : string;
  mutable outedges : edge list;
  mutable inedges : edge list;
  cfg : Cfg_core.cfg_node option;
}
and edge = {
  label : string;
  clabel : string;
  etype : etype;
  src : node;
  dest : node;
  file : string option;
}

val mk_node :
  string ->
  id ->
  ntype ->
  string ->
  edge list -> edge list -> Cfg_core.cfg_node option -> node
module Idmap :
  sig
    type key = int option
    type +'a t
    val empty : 'a t
    val is_empty : 'a t -> bool
    val add : key -> 'a -> 'a t -> 'a t
    val find : key -> 'a t -> 'a
    val remove : key -> 'a t -> 'a t
    val mem : key -> 'a t -> bool
    val iter : (key -> 'a -> unit) -> 'a t -> unit
    val map : ('a -> 'b) -> 'a t -> 'b t
    val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t
    val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
    val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
    val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
  end
val pp_dotty_transition_system : unit -> unit
val parameter : int -> string
exception Contained
val verify :
  string ->
  Cfg_core.cfg_node list ->
  Spec.spec -> Psyntax.logic -> Psyntax.logic -> bool
val verify_ensures :
  string ->
  Cfg_core.cfg_node list ->
  Psyntax.pform ->
  (Psyntax.pform -> Psyntax.form) ->
  Sepprover.inner_form list list -> Psyntax.logic -> Psyntax.logic -> unit
val bi_abduct :
  string ->
  Cfg_core.cfg_node list ->
  Spec.spec ->
  Psyntax.logic ->
  Psyntax.logic ->
  Psyntax.logic ->
  (Sepprover.inner_form * Sepprover.inner_form) list

(* TODO: This is only used by translatejimple in jstar, so perhaps it should not be here. *)
val get_frame :
  Cfg_core.cfg_node list ->
  Psyntax.pform ->
  Psyntax.logic -> Psyntax.logic -> Sepprover.inner_form list

