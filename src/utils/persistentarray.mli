(********************************************************
   This file is part of coreStar
        src/utils/persistentarray.mli
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   coreStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)


module type S =
  sig
    type elt
    type t
    val set : t -> int -> elt -> t
    val reset : t -> int -> t
    val get : t -> int -> elt
    val create : unit -> t
    val size : t -> int
    val grow : t -> int -> t
    val foldi : (int -> elt -> 'a -> 'a) -> t -> 'a -> 'a
    val find_indices : (elt -> bool) -> t -> int list
    (* After calling [unsafe_create a], don't dare to touch [a] again. *)
    val unsafe_create : elt array -> t
  end

module type CREATOR = sig
  type elt
  val create : int -> elt
end

(* NOTE: This is a functor so that you don't need to store a function [create]
in the data-structure [t].  If this was done (as it used to be, btw), then [t]s
cannot be compared (e.g., put in hashtables). *)

module Make (Creator : CREATOR) : S with type elt = Creator.elt
