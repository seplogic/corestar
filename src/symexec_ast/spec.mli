(********************************************************
   This file is part of coreStar
        src/symbexe_syntax/spec.mli
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   coreStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)


module ClassMap :
  sig
    type key = string
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
type excep_post = Psyntax.pform ClassMap.t
type spec = {
  pre : Psyntax.pform;
  post : Psyntax.pform;
  excep : excep_post;
}
val mk_spec :
  Psyntax.pform -> Psyntax.pform -> excep_post -> spec
val spec2str : Format.formatter -> spec -> unit
val specSet2str : Format.formatter -> spec HashSet.t -> unit
val pprinter_core_spec2str : spec -> string
val name_ret_v1 : string
val ret_v1 : Vars.var
val parameter : int -> string
val parameter_var : int -> Vars.var
