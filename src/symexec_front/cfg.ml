open Format
module C = Core

type cfg_vertex =
    Assign_cfg of C.call_core
  | Call_cfg of string * C.call_core
  | Nop_cfg
  (* NOTE: [Nop_cfg] gives some flexibility in choosing the shape of the graph.
  For example, [Procedure] below assumes one start and one stop node. *)

module Cfg = Graph.Imperative.Digraph.Abstract
  (struct type t = cfg_vertex end)

type state_transition =
  | Statement_st of Cfg.V.t
  | Nop_st
  (* TODO: Add other ways to evolve the state, such as implication. *)

module StateGraph (V : Graph.Sig.ANY_TYPE) =
  Graph.Imperative.Digraph.AbstractLabeled
    (V)
    (struct
      type t = state_transition
      let compare = compare
      let default = Nop_st
    end)

module MakeProcedure (Cfg : Graph.Sig.I ) = struct
  type t =
    { cfg : Cfg.t
    ; start : Cfg.vertex
    ; stop : Cfg.vertex }
end

module Procedure = MakeProcedure (Cfg)

module Display_Cfg = struct
  let vertex_name v = string_of_int (Hashtbl.hash v)
  let graph_attributes _ = []
  let default_vertex_attributes _ = []
  let vertex_attributes v = match Cfg.V.label v with
      Assign_cfg _ -> [`Label "Assign"]
    | Call_cfg (fname, _) -> [`Label ("Call " ^ fname)]
    | Nop_cfg -> [`Label "NOP"]
  let default_edge_attributes _ = []
  let edge_attributes _ = []
  let get_subgraph _ = None
end
module Dot_Cfg = Graph.Graphviz.Dot(struct
  include Display_Cfg
  include Cfg
end)

let fprint_Cfg = Dot_Cfg.fprint_graph

let print_Cfg = fprint_Cfg std_formatter

let output_Cfg = Dot_Cfg.output_graph

let fileout file_name f =
  try
    let o = open_out file_name in
      f o; close_out o
  with _ -> eprintf "@[Could not create file %s@." file_name

let fileout_Cfg file_name g =
  fileout file_name (fun o -> output_Cfg o g)

let fixpoint _ = failwith "TODO"

