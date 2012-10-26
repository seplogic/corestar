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
