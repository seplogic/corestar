open Format

module C = Core
module DG = Digraph
module P = Sepprover

type cfg_vertex =
  | Call_cfg of C.call_core
  | Abs_cfg
  | Nop_cfg
  (* NOTE: [Nop_cfg] gives some flexibility in choosing the shape of the graph.
  For example, [Procedure] below assumes one start and one stop node. *)

module Cfg = DG.Make (struct type t = cfg_vertex end) (DG.UnlabeledEdge)
module CfgVHashtbl = Hashtbl.Make (Cfg.V)
module CfgVHashSet = HashSet.Make (Cfg.V)

(* If [ss_missing_heap] is star-joined to the initial heap, then
  [ss_current_heap] is reached without fault.
  INV: [ss_missing_heap] must not mention program variables, only logical ones
*)
type symbolic_state =
  { ss_current_heap : P.inner_form
  ; ss_missing_heap : P.inner_form }

module StateGraph =
  DG.Make (struct type t = symbolic_state end) (DG.UnlabeledEdge)
module SgVHashtbl = Hashtbl.Make (StateGraph.V)
module SgVHashSet = HashSet.Make (StateGraph.V)

module MakeProcedure (Cfg : DG.IM) = struct
  type t =
    { cfg : Cfg.t
    ; start : Cfg.vertex
    ; stop : Cfg.vertex }
end

module Procedure = MakeProcedure (Cfg)

module Dot = DG.Dot (struct
  include DG.DotDefault (Cfg)
  let vertex_attributes v = match V.label v with
    | Call_cfg c -> [`Label c.C.call_name]
    | Abs_cfg -> [`Label "ABS"]
    | Nop_cfg -> [`Label "NOP"]
end)

let fileout file_name f =
  let o = open_out file_name in
  f o; close_out o

let fileout_cfg file_name g =
  fileout file_name (fun o -> Dot.output_graph o g)

let fixpoint _ = failwith "TODO"

