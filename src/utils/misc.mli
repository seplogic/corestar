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

(** {2} operations with strictly increasing lists *) (* {{{ *)
val remove_duplicates : ('a -> 'a -> int) -> 'a list -> 'a list
val merge_lists : 'a list -> 'a list -> 'a list
val insert_sorted : 'a -> 'a list -> 'a list

(* }}} *)

val iter_pairs : ('a -> 'a -> unit) -> 'a list -> unit
  (* Iterates over consecutive pairs. *)

val iter_all_pairs : ('a -> 'a -> unit) -> 'a list -> unit
  (* Iterates over all subsets of size 2. *)

val map_and_find : ('a -> 'b) -> 'a list -> 'b
  (** 
    [map_and_find f as] returns the result of the first successful
    application of [f] to an element of [as], or raises [Not_found] if
    all applications are unsuccsessful. The elements of [as] are tried in
    order. An application is successful when it raises no exception.
   *)

val lift_pair : ('a -> 'b) -> 'a * 'a -> 'b * 'b
val add_index : 'a list -> int -> ('a * int) list

val memo2 : ('a -> 'b -> 'c) -> ('a -> 'b -> 'c)
  (** [memo2 f] returns a memoized version of [f]. *)

val cross_product : ('a list) -> ('b list) -> (('a * 'b) list)

val fresh_int : unit -> unit -> int
  (** [fresh_int ()] is a generator for the sequence 0, 1, 2, ... *)

val hash_of_list
  : ('value -> 'summary) (* computes summary out of first value *)
    -> ('value -> 'summary -> 'summary) (* updates summary with a value *)
    -> ('elem -> 'key option)
    -> ('elem -> 'value option)
    -> 'elem list
    -> ('key, 'summary) Hashtbl.t
