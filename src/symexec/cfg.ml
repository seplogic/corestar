open Corestar_std
open Format

module C = Core
module DG = Digraph
module Expr = Expression

type cfg_vertex =
  | Abs_cfg
  | Call_cfg of C.call
  | Nop_cfg
  | Spec_cfg of C.spec
  (* NOTE: [Nop_cfg] gives some flexibility in choosing the shape of the graph.
  For example, [Procedure] below assumes one start and one stop node. *)

let pp_vertex f = function
  | Abs_cfg -> fprintf f "abstract"
  | Call_cfg c -> fprintf f "call %s" c.C.call_name
  | Nop_cfg -> fprintf f "nop"
  | Spec_cfg spec -> fprintf f "spec %a" CoreOps.pp_spec spec

module Cfg = DG.Make (struct type t = cfg_vertex end) (DG.UnlabeledEdge)
module CfgVHashtbl = Hashtbl.Make (Cfg.V)
module CfgVHashSet = HashSet.Make (Cfg.V)

(* If [missing_heap] is star-joined to the initial heap, then
  [current_heap] is reached without fault.
*)
type ok_configuration =
  { current_heap : Expr.t
  ; missing_heap : Expr.t (* should be [Expr.emp] if doing checking *)
  ; pvar_value : Expr.t StringMap.t }

let check_ok_configuration { current_heap; missing_heap; pvar_value } =
  let rec has_only_lvars e =
    Expr.cases Expr.is_lvar (fun _ -> List.for_all has_only_lvars) e in
  assert (has_only_lvars current_heap);
  assert (has_only_lvars missing_heap);
  let f v e = assert (Expr.is_pvar v); assert (has_only_lvars e) in
  StringMap.iter f pvar_value

let pp_ok_configuration f { current_heap; missing_heap; pvar_value } =
  let ds = StringMap.bindings pvar_value in
  let pd f (v, e) = fprintf f "%s=%a" v Expr.pp e in
  fprintf f "(defs:%a,@ now:%a,@ missing:%a)"
    (pp_list_sep " * " pd) ds
    Expr.pp current_heap
    Expr.pp missing_heap

type split_type = Angelic | Demonic

let pp_split_type f = function
  | Angelic -> fprintf f "angelic"
  | Demonic -> fprintf f "demonic"

type configuration = ErrorConf | OkConf of ok_configuration * split_type

let pp_configuration f = function
  | ErrorConf -> fprintf f "Error"
  | OkConf (c, st) -> fprintf f "%a: %a" pp_split_type st pp_ok_configuration c

(* TODO: Explain the semantics of the configuration graph.
The basic idea is that lvars are like free variables in logic: you first
instantiate them with some constant accross the whole confgraph, and no matter
which constants you picked, the result accurately describes the program. *)
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
    let l x = `Label (Dot.escape_for_label x) in
    match V.label v with
    | Abs_cfg -> [ l "ABS";  `Color "lightblue"; `Shape `Ellipse; `Style [`Filled] ]
    | Call_cfg c -> [ l c.C.call_name; `Shape `Box ]
    | Nop_cfg -> [ l "NOP"; `Shape `Ellipse ]
    | Spec_cfg s ->
        let m = get_margin () in
        set_margin 40;
        let lbl = string_of CoreOps.pp_spec s in
        set_margin m;
        [ l lbl; `Shape `Box; `Style [`Rounded] ]
end)

let fileout file_name f =
  let o = open_out file_name in
  f o; close_out o

let fileout_cfg file_name g =
  fileout file_name (fun o -> DotCfg.output_graph o g)

let fileout_confgraph stops file_name g =
  let module DotConf = DG.Dot (struct
    include DG.DotDefault (ConfigurationGraph)
    let vertex_attributes v =
      let color =
        match V.label v with ErrorConf -> "red" | OkConf _ -> "black" in
      let shape =
        match V.label v with ErrorConf -> `Ellipse | OkConf _ -> `Box in
      let style =
        (if CVHashSet.mem stops v then [ `Bold ] else [])
        @ [match V.label v with ErrorConf -> `Filled | OkConf _ -> `Rounded] in
      let presentation = [ `Color color; `Shape shape; `Style style ] in
      let l x = `Label (Dot.escape_for_label x) in
      fprintf str_formatter "%a" pp_configuration (V.label v);
      let s = flush_str_formatter () in
      l s :: presentation
  end) in
  fileout file_name (fun o -> DotConf.output_graph o g)
