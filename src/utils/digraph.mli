(* NOTE(rgrig): This interface is similar to that of OCamlGraph.
I am forced not to use OCamlGraph, because of the licence. *)

module type ANY_TYPE = sig type t end
module type ORDERED_TYPE_DFT =
  sig type t val compare : t -> t -> int val default : t end
module type COMPARABLE = sig
  type t
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val hash : t -> int
end
module UnlabeledEdge : ORDERED_TYPE_DFT
module type VERTEX =
  sig
    type t
    val compare : t -> t -> int
    val hash : t -> int
    val equal : t -> t -> bool
    type label
    val create : label -> t
    val label : t -> label
  end
module type EDGE =
  sig
    type t
    val compare : t -> t -> int
    type vertex
    val src : t -> vertex
    val dst : t -> vertex
    type label
    val create : vertex -> label -> vertex -> t
    val label : t -> label
  end
module type IM =
  sig
    type t
    module V : VERTEX
    type vertex = V.t
    module E : EDGE with type vertex = vertex
    type edge = E.t
    val iter_vertex : (vertex -> unit) -> t -> unit
    val iter_edges : (vertex -> vertex -> unit) -> t -> unit
    val iter_edges_e : (edge -> unit) -> t -> unit
    val iter_succ : (vertex -> unit) -> t -> vertex -> unit
    val create : ?size:int -> unit -> t
    val add_vertex : t -> vertex -> unit
    val add_edge : t -> vertex -> vertex -> unit
  end
module Make :
  functor (Vl : ANY_TYPE) ->
  functor (El : ORDERED_TYPE_DFT) ->
  IM with type V.label = Vl.t and type E.label = El.t
module DotAttributes :
  sig
    type shape =
        [ `Box
        | `Circle
        | `Diamond
        | `Doublecircle
        | `Ellipse
        | `Plaintext
        | `Polygon of int * float
        | `Record ]
    type graph = [ `Center of bool ]
    type vertex = [ `Label of string | `Shape of shape ]
    type edge = [ `Arrowsize of float ]
  end
module type DISPLAY = sig
  type t
  module V : VERTEX
  module E : EDGE with type vertex = V.t
  val iter_vertex : (V.t -> unit) -> t -> unit
  val iter_edges_e : (E.t -> unit) -> t -> unit
  val graph_attributes : t -> DotAttributes.graph list
  val default_vertex_attributes : t -> DotAttributes.vertex list
  val vertex_name : V.t -> string
  val vertex_attributes : V.t -> DotAttributes.vertex list
  val default_edge_attributes : t -> DotAttributes.edge list
  val edge_attributes : E.t -> DotAttributes.edge list
end
module DotDefault : functor (G : IM) ->
  DISPLAY with type t = G.t and module V = G.V and module E = G.E
module Dot : functor (X : DISPLAY) -> sig
  val fprint_graph : Format.formatter -> X.t -> unit
  val output_graph : out_channel -> X.t -> unit
end
module Components : sig
  module type G = sig
    type t
    module V : COMPARABLE
    val iter_vertex : (V.t -> unit) -> t -> unit
    val iter_succ : (V.t -> unit) -> t -> V.t -> unit
  end
  module Make : functor (G : G) -> sig
    val scc : G.t -> int * (G.V.t -> int)
    val scc_array : G.t -> G.V.t list array
    val scc_list : G.t -> G.V.t list list
  end
end
