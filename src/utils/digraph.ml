(* XXX: Infer and fix digraph.mli *)
open Debug
open Format

module type ANY_TYPE = sig type t end

module type ORDERED_TYPE_DFT = sig
  include Set.OrderedType
  val default : t
end

module type VERTEX = sig
  type t
  val compare : t -> t -> int
  val hash : t -> int
  val equal : t -> t -> bool
  type label
  val create : label -> t
  val label : t -> label
end

module type EDGE = sig
  type t
  val compare : t -> t -> int
  type vertex
  val src : t -> vertex
  val dst : t -> vertex
  type label
  val create : vertex -> label -> vertex -> t
  val label : t -> label
end

(* TODO(rgrig): Grab stuff from
file:///usr/share/doc/libocamlgraph-ocaml-doc/html/api/Sig.IM.html *)
module type IM = sig
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

let fresh_vertex_id = Misc.fresh_int ()
let fresh_edge_id = Misc.fresh_int ()

module Make (Vl : ANY_TYPE) (El : ORDERED_TYPE_DFT)
: IM with type V.label = Vl.t and type E.label = El.t
= struct
  module V : VERTEX with type label = Vl.t = struct
    type label = Vl.t
    type t = { id : int; label : label }
    let compare x y = compare x.id y.id
    let hash x = x.id
    let equal x y = x.id = y.id
    let create label = { id = fresh_vertex_id (); label }
    let label x = x.label
  end

  type vertex = V.t

  module E : EDGE with type vertex = vertex and type label = El.t = struct
    type vertex = V.t
    type label = El.t
    type t = { id : int; src : vertex; label : label; dst : vertex }
    let compare e f = compare e.id f.id
    let src e = e.src
    let dst e = e.dst
    let label e = e.label
    let create src label dst = { id = fresh_edge_id (); src; label; dst }
  end

  type edge = E.t

  module ESet = Set.Make (E)
  module VMap = Hashtbl.Make (V)

  type t =
    { out_edges : ESet.t VMap.t
    ; in_edges : ESet.t VMap.t }

  let iter_vertex f g =
    let f x _ = f x in
    VMap.iter f g.out_edges

  let iter_edges_e f g =
    let f _ es = ESet.iter f es in
    VMap.iter f g.out_edges

  (* NOTE: Successors may be iterated multiple times in multigraphs. *)
  let iter_succ f g x =
    let es =
      try VMap.find g.out_edges x
      with Not_found -> raise (Invalid_argument "iter_succ") in
    let f e = f (E.dst e) in
    ESet.iter f es

  let create ?(size = 1) () =
    { out_edges = VMap.create size
    ; in_edges = VMap.create size }

  let add_vertex g x =
    let add x h = if not (VMap.mem h x) then VMap.add h x ESet.empty in
    add x g.out_edges;
    add x g.in_edges

  let add_edge g x y =
    add_vertex g x;
    add_vertex g y;
    let e = E.create x El.default y in
    let add x h = VMap.replace h x (ESet.add e (VMap.find h x)) in
    add x g.out_edges;
    add y g.in_edges
end

module DotAttributes = struct
  type shape =
    [ `Box
    | `Circle
    | `Diamond
    | `Doublecircle
    | `Ellipse
    | `Plaintext
    | `Polygon of int * float
    | `Record ]

  type graph =
    [ `Center of bool ]

  type vertex =
    [ `Label of string
    | `Shape of shape ]

  type edge =
    [ `Arrowsize of float ]
end

module Dot = functor
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
    val edge_attributes : E.t -> DotAttributes.edge list end)
-> struct
  let fprint_attribute f = function
    | `Label s -> fprintf f "label=\"%s\"" s
    | `Shape x -> fprintf f "shape=";
        (match x with
        | `Box -> fprintf f "box"
        | #DotAttributes.shape -> failwith "TODO")
    | #DotAttributes.vertex
    | #DotAttributes.edge
    | #DotAttributes.graph -> failwith "TODO"

  let fprint_attribute_list f =
    let rec fa_nel f = function
      | [] -> assert false
      | [x] -> fprintf f "%a" fprint_attribute x
      | x :: xs -> fprintf f "%a,@,%a" fprint_attribute x fa_nel xs in
    function
      | [] -> ()
      | xs -> fprintf f " @[<2>[%a]@]" fa_nel xs

  let fprint_vertex f x =
    let xas = X.vertex_attributes x in
    fprintf f "@\n%s%a;" (X.vertex_name x) fprint_attribute_list xas

  let fprint_edge f e =
    let src = X.vertex_name (X.E.src e) in
    let dst = X.vertex_name (X.E.dst e) in
    let eas = X.edge_attributes e in
    fprintf f "@\n%s -> %s%a;" src dst fprint_attribute_list eas

  (* TODO(rgrig): Handle default attributes. *)
  let fprint_graph f g =
    fprintf f "@[@[<2>digraph G{";
    X.iter_vertex (fprint_vertex f) g;
    X.iter_edges_e (fprint_edge f) g;
    fprintf f "@]@\n}@\n@]"

  let output_graph out g =
    let f = formatter_of_out_channel out in
    let m = get_margin () in
    set_margin 80; fprintf f "%a@?" fprint_graph g; set_margin m
end
