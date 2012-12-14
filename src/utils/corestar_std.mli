(********************************************************
   This file is part of coreStar
        src/utils/corestar_std.mli
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   coreStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)


(** Contains utilities that we'd like to have had in OCaml's stdlib. *)

(* {{{ *) (** {2 Common operations} *)

(**
  Function composition. Where a function is expected, you can write [g @@
  f] instead of [fun x -> g (f x)].
 *)
val ( @@ ) : ('b -> 'c) -> ('a -> 'b) -> ('a -> 'c)

(** Function feeding. You can write [x |> f |> g] instead of [g (f (x))]. *)
val ( |> ) : 'a -> ('a -> 'b) -> 'b

(** Function application. You can write [g & f & x] instead of [g (f (x))]. *)
val ( & ) : ('a -> 'b) -> 'a -> 'b

(** [xs =:: x] prepends [x] to [xs] *)
val ( =:: ) : 'a list ref -> 'a -> unit

(** Shortcut for [Lazy.force]. *)
val ( !* ) : 'a Lazy.t -> 'a

(** Converts an uncurried function into a curried one. *)
val curry : ('a * 'b -> 'c) -> 'a -> 'b -> 'c

(** Converts a curried function into an uncurried one. *)
val uncurry : ('a -> 'b -> 'c) -> 'a * 'b -> 'c

(** Like in Haskell. *)
val option : 'b -> ('a -> 'b) -> 'a option -> 'b

(** Map for options. *)
val option_map : ('a -> 'b) -> 'a option -> 'b option

(** Like in Haskell. *)
val map_option : ('a -> 'b option) -> 'a list -> 'b list

(** Like in Haskell. *)
val from_option : 'a -> ('a option) -> 'a

(** Like in Haskell. *)
val is_some : 'a option -> bool

(** Like in Haskell. *)
val is_none : 'a option -> bool

(** Flip the first two arguments of a function. *)
val flip : ('a -> 'b -> 'c) -> ('b -> 'a -> 'c)

(* }}} *)
(* {{{ *) (** {2 Sets and maps} *)

(** A set of strings. *)
module StringSet : Set.S with type elt = string

(** A set of integers. *)
module IntSet : Set.S with type elt = int

(** A map from strings to something. *)
module StringMap : Map.S with type key = string

(**
  A few helpers for dealing with maps. This is a workaround for the lack of
  some functions in the standard Map.S module. Whenever you define a map
  [module M = Map.Make (...)] you can also define [module MH = MapHelper
  (M)]. Normal functions like [M.fold] are used as before, but you can also
  say things like [MH.filter].

  Should be removed once we move to OCaml 3.12.
 *)
module MapHelper :
  functor (M : Map.S) -> sig
    (**
      [filter p m] returns a map with all the keys that satisfy predicate
      [p]. Takes O(|m|+|n| lg |n|) time, where [n] is the result.
     *)
    val filter : (M.key -> 'a -> bool) -> 'a M.t -> 'a M.t
  end

module HashtblH : sig
  (** Builds a hashtable from an association list. *)
  val of_list : ('a * 'b) list -> ('a, 'b) Hashtbl.t
end
(* }}} *)
(* {{{ *) (** {2 String and char utilities} *)

(** Functions missing from [Char]. *)
module CharH : sig
  (** Same as the C function [isspace] in the POSIX locale. *)
  val is_space : char -> bool
end

(** Functions missing from [String]. *)
module StringH : sig
  (**
    Removes the longest prefix and the longest suffix made entierly of
    spaces. In particular, it returns the empty string if the input is all
    spaces.
  *)
  val trim : string -> string

  (** [starts_with prefix s] says whether [s] starts with [prefix]. *)
  val starts_with : string -> string -> bool

  (** [ends_with suffix s] says whether [s] ends with [suffix]. *)
  val ends_with : string -> string -> bool
end

(* }}} *)
(* {{{ *) (** {2 List and array utilities} *)
module ListH : sig
  val init : int -> (int -> 'a) -> 'a list
    (** Like [Array.init]. *)
end

val cons : 'a -> 'a list -> 'a list
(* }}} *)
(* {{{ *) (** {2 Pretty printing} *)
val pp_string : Format.formatter -> string -> unit

val pp_list :
  (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a list -> unit

val pp_list_sep :
  string
  -> (Format.formatter -> 'a -> unit)
  -> Format.formatter
  -> 'a list
  -> unit
(* }}} *)
