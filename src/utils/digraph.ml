open Corestar_std
open Debug
open Format

module type ANY_TYPE = sig type t end

module type ORDERED_TYPE_DFT = sig
  include Set.OrderedType
  val default : t
end

module type COMPARABLE = sig
  include Set.OrderedType
  include Hashtbl.HashedType with type t := t
end

module UnlabeledEdge : ORDERED_TYPE_DFT = struct
  type t = unit
  let compare = compare
  let default = ()
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
  val out_degree : t -> vertex -> int
  val in_degree : t -> vertex -> int
  val iter_vertex : (vertex -> unit) -> t -> unit
  val fold_vertex : (vertex -> 'a -> 'a) -> t -> 'a -> 'a
  val iter_edges : (vertex -> vertex -> unit) -> t -> unit
  val iter_edges_e : (edge -> unit) -> t -> unit
  val iter_succ : (vertex -> unit) -> t -> vertex -> unit
  val iter_pred : (vertex -> unit) -> t -> vertex -> unit
  val fold_succ : (vertex -> 'a -> 'a) -> t -> vertex -> 'a -> 'a
  val fold_pred : (vertex -> 'a -> 'a) -> t -> vertex -> 'a -> 'a
  val create : ?size:int -> unit -> t
  val add_vertex : t -> vertex -> unit
  val remove_vertex : t -> vertex -> unit
  val add_edge : t -> vertex -> vertex -> unit
  val remove_edge : t -> vertex -> vertex -> unit
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

  let degree es x =
    try ESet.cardinal (VMap.find es x)
    with Not_found -> raise (Invalid_argument "vertex not in graph")

  let out_degree g = degree g.out_edges
  let in_degree g = degree g.in_edges

  let iter_vertex f g =
    let f x _ = f x in
    VMap.iter f g.out_edges

  let fold_vertex f g =
    let f x _ = f x in
    VMap.fold f g.out_edges

  let iter_edges_e f g =
    let f _ es = ESet.iter f es in
    VMap.iter f g.out_edges

  let iter_edges f g =
    let f e = f (E.src e) (E.dst e) in
    iter_edges_e f g

  (* NOTE: Succs/Preds may be iterated multiple times in multigraphs. *)
  let iter_pred_or_succ f es tip x =
    let es =
      try VMap.find es x
      with Not_found -> invalid_arg "iter_pred_or_succ" in
    let f e = f (tip e) in
    ESet.iter f es

  let iter_succ f g = iter_pred_or_succ f g.out_edges E.dst
  let iter_pred f g = iter_pred_or_succ f g.in_edges E.src
  let fold_succ _ = failwith "todo"
  let fold_pred _ = failwith "todo"

  let create ?(size = 1) () =
    { out_edges = VMap.create size
    ; in_edges = VMap.create size }

  let add_vertex g x =
    let add x h = if not (VMap.mem h x) then VMap.add h x ESet.empty in
    add x g.out_edges;
    add x g.in_edges

  let remove_vertex g x =
    VMap.remove g.out_edges x;
    VMap.remove g.in_edges x

  let add_edge g x y =
    add_vertex g x;
    add_vertex g y;
    let e = E.create x El.default y in
    let add x h = VMap.replace h x (ESet.add e (VMap.find h x)) in
    add x g.out_edges;
    add y g.in_edges

  let remove_edge g x y =
    try
      let wy = VMap.find g.out_edges x in
      let wx = VMap.find g.in_edges y in
      let woy = ESet.filter (fun e -> not (V.equal y (E.dst e))) wy in
      let wox = ESet.filter (fun e -> not (V.equal x (E.src e))) wx in
      VMap.replace g.out_edges x woy;
      VMap.replace g.in_edges y wox
    with Not_found -> invalid_arg "remove_edge"
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

module DotDefault (G : IM) = struct
  include G
  let vertex_name v = string_of_int (V.hash v)
  let graph_attributes _ = []
  let default_vertex_attributes _ = []
  let vertex_attributes _ = []
  let default_edge_attributes _ = []
  let edge_attributes _ = []
end

module Dot (X : DISPLAY) = struct
  let fprint_attribute f = function
    | `Label s -> fprintf f "label=\"%s\"" s
    | `Shape x -> fprintf f "shape=";
        (match x with
        | `Box -> fprintf f "box"
        | #DotAttributes.shape -> failwith "TODO")
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

module Components = struct
  module type G = sig
    type t
    module V : COMPARABLE
    val iter_vertex : (V.t -> unit) -> t -> unit
    val iter_succ : (V.t -> unit) -> t -> V.t -> unit
  end

  module Make (G : G) = struct
    (* NOTE: The requirements on G are too weak to allow a nicer construction
    of reverse(G). *)

    module VH = Hashtbl.Make (G.V)

    (* Ensures that all vertices appear as keys in the result. *)
    let reverse g =
      let gr = VH.create 1 in
      let pe v u =
        let succ_u = try VH.find gr u with Not_found -> VH.create 1 in
        VH.replace succ_u v ();
        VH.replace gr u succ_u;
        if not (VH.mem gr v) then VH.add gr v (VH.create 1) in
      let pv v = G.iter_succ (pe v) g v in
      G.iter_vertex pv g;
      gr

    let rev_postorder_of_rev g =
      let gr = reverse g in
      let r = ref [] in
      let seen = VH.create 1 in
      let rec dfs_r v () =
        if not (VH.mem seen v) then begin
          VH.add seen v ();
          (try VH.iter dfs_r (VH.find gr v) with Not_found -> ());
          r =:: v
        end in
      (* Assumes all vertices appear as keys. *)
      VH.iter (fun v _ -> dfs_r v ()) gr;
      !r

    let scc g =
      let idx = VH.create 1 in
      let n = ref (-1) in
      let rec dfs u =
        if not (VH.mem idx u) then begin
          VH.add idx u !n;
          G.iter_succ dfs g u
        end in
      let pc u = if not (VH.mem idx u) then (incr n; dfs u) in
      List.iter pc (rev_postorder_of_rev g);
      (!n + 1, VH.find idx)

    let scc_array g =
      let n, idx = scc g in
      let r = Array.make n [] in
      let pv v =
        let i = idx v in
        r.(i) <- v :: r.(i) in
      G.iter_vertex pv g;
      r

    let scc_list g = Array.to_list (scc_array g)
  end
end
