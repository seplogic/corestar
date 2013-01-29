(* A sub-type of [HashSet.S]. *)
module type SET = sig
  type elt
  type t
  val add : t -> elt -> unit
  val create : int -> t
  val elements : t -> elt list
  val mem : t -> elt -> bool
  val remove : t -> elt -> unit
end
module type S = sig
  type elt
  type t

  val initialize : bool -> t
    (* The argument says whether [elt]s are processed at most once. *)

  val enque : t -> elt -> unit
    (* Enques an element, unless it was seen. *)

  val deque : t -> elt
    (* Deques an element. Forgets seeing the element when initialized without
    the restriction to process elements at most once. *)

  val is_done : t -> bool

  val is_seen : t -> elt -> bool

  val get_seen : t -> elt list
end
module Make : functor (H : SET) -> S with type elt = H.elt
