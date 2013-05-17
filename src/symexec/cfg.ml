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

let pp_vertex f = function
  | Abs_cfg -> fprintf f "abstract"
  | Call_cfg c -> fprintf f "call %s" c.C.call_name
  | Nop_cfg -> fprintf f "nop"
  | Spec_cfg specs -> HashSet.iter (fun s -> fprintf f "spec {%a} " CoreOps.pp_inner_triple s) specs

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

let pp_ok_configuration f { current_heap; missing_heap } =
  fprintf f "(now:%a,@ missing:%a)"
    Sepprover.string_inner_form current_heap
    Sepprover.string_inner_form missing_heap
    
type split_type = Angelic | Demonic

let pp_split_type f = function
  | Angelic -> fprintf f "angelic"
  | Demonic -> fprintf f "demonic"

type configuration = ErrorConf | OkConf of ok_configuration * split_type

let pp_configuration f = function
  | ErrorConf -> fprintf f "Error"
  | OkConf (c, st) -> fprintf f "%a: %a" pp_split_type st pp_ok_configuration c

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

module DotCfg = DG.Dot (struct
  include DG.DotDefault (Cfg)
  let vertex_attributes v =
    let l x = [ `Label (Dot.escape_for_label x) ] in
    match V.label v with
    | Abs_cfg -> l "ABS"
    | Call_cfg c -> l c.C.call_name
    | Nop_cfg -> l "NOP"
    | Spec_cfg s -> l (string_of CoreOps.pp_inner_spec s)
end)

module DotConf = DG.Dot (struct
  include DG.DotDefault (ConfigurationGraph)
  let vertex_attributes v =
    let l x = [ `Label (Dot.escape_for_label x) ] in
    fprintf str_formatter "%a" pp_configuration (V.label v);
    let s = flush_str_formatter () in
    l s
end)

let fileout file_name f =
  let o = open_out file_name in
  f o; close_out o

let fileout_cfg file_name g =
  fileout file_name (fun o -> DotCfg.output_graph o g)

let fileout_confgraph file_name g =
  fileout file_name (fun o -> DotConf.output_graph o g)
