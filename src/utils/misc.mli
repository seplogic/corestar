(********************************************************
   This file is part of coreStar
        src/utils/misc.mli
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   coreStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)

(** Utilities that do not clearly fit in any other module. *)

type ('a, 'b) sum = Inr of 'a | Inl of 'b
val remove_duplicates : ('a -> 'a -> int) -> 'a list -> 'a list
val intcmp : 'a -> 'a -> int
val intcmp2 : 'a * 'b -> 'a * 'b -> int

val iter_pairs : ('a -> 'a -> unit) -> 'a list -> unit

val map_and_find : ('a -> 'b) -> 'a list -> 'b
  (** 
    [map_and_find f as] returns the result of the first successful
    application of [f] to an element of [as], or raises [Not_found] if
    all applications are unsuccsessful. The elements of [as] are tried in
    order. An application is successful when it raises no exception.
   *)

val find_no_match_simp : ('a -> 'b) -> 'a list -> 'b
val lift_pair : ('a -> 'b) -> 'a * 'a -> 'b * 'b
val add_index : 'a list -> int -> ('a * int) list

val memo2 : ('a -> 'b -> 'c) -> ('a -> 'b -> 'c)
  (** [memo2 f] returns a memoized version of [f]. *)

val cross_product : ('a list) -> ('b list) -> (('a * 'b) list)

val fresh_int : unit -> unit -> int
  (** [fresh_int ()] is a generator for the sequence 0, 1, 2, ... *)
