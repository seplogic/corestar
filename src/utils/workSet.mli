type 'a t
val create : int -> 'a t
val perform_work : 'a t -> (('a -> unit) -> 'a -> unit) -> unit
val singleton : 'a -> 'a t
