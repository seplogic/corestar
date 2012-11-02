open Format
open Digraph
module C = Core

type cfg_vertex =
  | Call_cfg of C.call_core
  | Nop_cfg
  (* NOTE: [Nop_cfg] gives some flexibility in choosing the shape of the graph.
  For example, [Procedure] below assumes one start and one stop node. *)

module Cfg = Digraph.Make
  (struct type t = cfg_vertex end)
  (struct type t = unit let compare = compare let default = () end)

type state_transition =
  | Statement_st of Cfg.V.t
  | Nop_st
  (* TODO: Add other ways to evolve the state, such as implication. *)

module StateGraph (V : Digraph.ANY_TYPE) = Digraph.Make
  (V)
  (struct
    type t = state_transition
    let compare = compare
    let default = Nop_st
  end)

module MakeProcedure (Cfg : Digraph.IM) = struct
  type t =
    { cfg : Cfg.t
    ; start : Cfg.vertex
    ; stop : Cfg.vertex }
end

module Procedure = MakeProcedure (Cfg)

module Dot = Digraph.Dot (struct
  include Digraph.DotDefault (Cfg)
  let vertex_attributes v = match V.label v with
    | Call_cfg c -> [`Label c.C.call_name]
    | Nop_cfg -> [`Label "NOP"]
end)

let fileout file_name f =
  let o = open_out file_name in
  f o; close_out o

let fileout_cfg file_name g =
  fileout file_name (fun o -> Dot.output_graph o g)

let fixpoint _ = failwith "TODO"

