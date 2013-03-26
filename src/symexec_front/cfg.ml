open Corestar_std
open Format

module C = Core
module DG = Digraph
module P = Sepprover

type cfg_vertex =
  | Abs_cfg
  | Call_cfg of C.call_core
  | Nop_cfg
  | Spec_cfg of C.inner_spec
  (* NOTE: [Nop_cfg] gives some flexibility in choosing the shape of the graph.
  For example, [Procedure] below assumes one start and one stop node. *)

module Cfg = DG.Make (struct type t = cfg_vertex end) (DG.UnlabeledEdge)
module CfgVHashtbl = Hashtbl.Make (Cfg.V)
module CfgVHashSet = HashSet.Make (Cfg.V)

(* If [missing_heap] is star-joined to the initial heap, then
  [current_heap] is reached without fault.
  INV: [missing_heap] must not mention program variables, only logical ones
*)
type ok_configuration =
  { current_heap : P.inner_form
  ; missing_heap : P.inner_form }

type split_type = Angelic | Demonic
type configuration = ErrorConf | OkConf of ok_configuration * split_type

module ConfigurationGraph =
  DG.Make (struct type t = configuration end) (DG.UnlabeledEdge)
module CVHashtbl = Hashtbl.Make (ConfigurationGraph.V)
module CVHashSet = HashSet.Make (ConfigurationGraph.V)

module MakeProcedure (Cfg : DG.IM) = struct
  type t =
    { cfg : Cfg.t
    ; start : Cfg.vertex
    ; stop : Cfg.vertex }
end

module Procedure = MakeProcedure (Cfg)

module Dot = DG.Dot (struct
  include DG.DotDefault (Cfg)
  let vertex_attributes v =
    let l x = [ `Label x ] in
    match V.label v with
    | Abs_cfg -> l "ABS"
    | Call_cfg c -> l c.C.call_name
    | Nop_cfg -> l "NOP"
    | Spec_cfg s -> l (string_of CoreOps.pp_inner_spec s)
end)

let fileout file_name f =
  let o = open_out file_name in
  f o; close_out o

let fileout_cfg file_name g =
  fileout file_name (fun o -> Dot.output_graph o g)

let fixpoint _ = failwith "TODO"

