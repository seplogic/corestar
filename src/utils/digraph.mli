(* NOTE(rgrig): This interface is similar to that of OCamlGraph.
I am forced not to use OCamlGraph, because of the licence. *)

module type ANY_TYPE = sig type t end
module type ORDERED_TYPE_DFT =
  sig type t val compare : t -> t -> int val default : t end
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
module DotDefault :
  sig
    val graph_attributes : 'g -> DotAttributes.graph list
    val default_vertex_attributes : 'g -> DotAttributes.vertex list
    val vertex_name : 'v -> string
    val vertex_attributes : 'v -> DotAttributes.vertex list
    val default_edge_attributes : 'g -> DotAttributes.edge list
    val edge_attributes : 'e -> DotAttributes.edge list
  end
module Dot :
  functor
    (X : sig
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
         end) ->
    sig
      val fprint_graph : Format.formatter -> X.t -> unit
      val output_graph : out_channel -> X.t -> unit
    end
