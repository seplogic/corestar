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
  val enque : t -> elt -> unit
  val deque : t -> elt
  val is_done : t -> bool
  val is_seen : t -> elt -> bool
  val get_seen : t -> elt list
end

module Make (H : SET) = struct
  type elt = H.elt
  type t = { que : elt Queue.t; seen : H.t; once : bool }

  let initialize once = { que = Queue.create (); seen = H.create 1; once }

  let enque { que; seen; _ } x =
    if not (H.mem seen x) then (H.add seen x; Queue.push x que)

  let deque { que; seen; once } =
    let x = Queue.pop que in
    if not once then H.remove seen x;
    x

  let is_done { que; _ } = Queue.is_empty que

  let is_seen { seen; _ } x = H.mem seen x

  let get_seen { seen; _ } = H.elements seen
end
