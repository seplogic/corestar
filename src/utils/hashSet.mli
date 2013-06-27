type 'a t
val add : 'a t -> 'a -> unit
val choose : 'a t -> 'a
val create : int -> 'a t
val elements : 'a t -> 'a list
val iter : ('a -> unit) -> 'a t -> unit
val fold : ('a -> 'b -> 'b) -> 'a t -> 'b -> 'b
val for_all : ('a -> bool) -> 'a t -> bool
val exists : ('a -> bool) -> 'a t -> bool
val length : 'a t -> int
val mem : 'a t -> 'a -> bool
val find : 'a t -> 'a -> unit
val remove : 'a t -> 'a -> unit
val singleton : 'a -> 'a t
val of_list : 'a list -> 'a t
val map : ('a -> 'b) -> 'a t -> 'b t

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
  val for_all : (elt -> bool) -> t -> bool
  val exists : (elt -> bool) -> t -> bool
  val length : t -> int
  val mem : t -> elt -> bool
  val find : t -> elt -> unit
  val remove : t -> elt -> unit
  val singleton : elt -> t
  val of_list : elt list -> t
(* XXX:  val map : (elt -> 'a) -> t -> (S with type elt = 'a).t *)
end
module Make : functor (E : HashedType) -> S with type elt = E.t
