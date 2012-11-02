(* TODO(rgrig): Functorial interface when we'll need it. *)

type 'a t
val add : 'a t -> 'a -> unit
val choose : 'a t -> 'a
val create : int -> 'a t
val elements : 'a t -> 'a list
val iter : ('a -> unit) -> 'a t -> unit
val fold : ('a -> 'b -> 'b) -> 'a t -> 'b -> 'b
val length : 'a t -> int
val mem : 'a t -> 'a -> bool
val remove : 'a t -> 'a -> unit
val singleton : 'a -> 'a t

module type HashedType = Hashtbl.HashedType
module type S = sig
  type elt
  type t
  val add : t -> elt -> unit
  val choose : t -> elt
  val create : int -> t
  val elements : t -> elt list
  val iter : (elt -> unit) -> t -> unit
  val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a
  val length : t -> int
  val mem : t -> elt -> bool
  val remove : t -> elt -> unit
  val singleton : elt -> t
end
module Make : functor (E : HashedType) -> S with type elt = E.t
