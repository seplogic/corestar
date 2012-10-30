(** Entry point for experiments on abduction with procedure calls. *)

open Corestar_std
open Debug
open Format
module C = Core
module G = Cfg

exception Fatal of string

let verbose = ref 0

let parse fn =
  System.parse_file Parser.symb_question_file Lexer.token fn "core"

let fresh_asgn_proc =
  let fi = Misc.fresh_int () in
  fun () -> sprintf "@[assignment %d@]" (fi ())
  (* NOTE: the space in the ID is intended: it should be unparseable *)

let desugar_assignments ps =
  let qs = ref [] in (* dummy procedures that simulate assignments *)
  let d_stmt = function
    | C.Assignment_core { C.asgn_rets; asgn_args; asgn_spec } ->
        let name = fresh_asgn_proc () in
        qs =:: { C.proc_name = name; proc_spec = asgn_spec; proc_body = None };
        C.Call_core
          { C.call_name = name; call_rets = asgn_rets; call_args = asgn_args }
    | s -> s in
  let d_body = List.map d_stmt in
  let d_proc p = { p with C.proc_body = option_map d_body p.C.proc_body } in
  let ps = List.map d_proc ps in
  List.rev_append ps !qs

(* helpers for [mk_intermediate_cfg] {{{ *)
module CfgH = Digraph.Make
  (struct type t = C.core_statement end)
  (Digraph.UnlabeledEdge)
module HVHashtbl = Hashtbl.Make (CfgH.V)

module ProcedureH = G.MakeProcedure (CfgH)

let fileout f file_name g = G.fileout file_name (fun o -> f o g)

module DotH = Digraph.Dot (struct
  include CfgH
  include Digraph.DotDefault
  let vertex_attributes v = match CfgH.V.label v with
      C.Nop_stmt_core -> [`Label "NOP"]
    | C.Label_stmt_core s -> [`Label ("Label:" ^ s)]
    | C.Assignment_core _ -> [`Label "Assign "; `Shape `Box]
    | C.Call_core c -> [`Label ("Call " ^ c.C.call_name); `Shape `Box]
    | C.Goto_stmt_core ss -> [`Label ("Goto:" ^ (String.concat "," ss))]
    | C.End -> [`Label "End"]
end)
let fileout_cfgH = fileout DotH.output_graph

let mic_create_vertices g cs =
  let succ = HVHashtbl.create 1 in
  let cs = C.Nop_stmt_core :: cs @ [C.Nop_stmt_core] in
  let vs = List.map CfgH.V.create cs in
  List.iter (CfgH.add_vertex g) vs;
  Misc.iter_pairs (HVHashtbl.add succ) vs;
  List.hd vs, List.hd (List.rev vs), succ

let mic_hash_labels g =
  let labels = Hashtbl.create 1 in
  let f v = match CfgH.V.label v with
    | C.Label_stmt_core l -> Hashtbl.add labels l v
    | _ -> () in
  CfgH.iter_vertex f g;
  labels

let mic_add_edges r labels succ =
  let g = r.ProcedureH.cfg in
  let vertex_of_label l =
    try Hashtbl.find labels l
    with Not_found -> raise (Fatal ("label " ^ l ^ " is missing")) in
  let add_outgoing x = if not (CfgH.V.equal x r.ProcedureH.stop) then begin
      match CfgH.V.label x with
      | C.Goto_stmt_core ls ->
          List.iter (fun l -> CfgH.add_edge g x (vertex_of_label l)) ls
      | C.End -> CfgH.add_edge g x r.ProcedureH.stop
      | _  -> CfgH.add_edge g x (HVHashtbl.find succ x)
    end in
  CfgH.iter_vertex add_outgoing g

(* }}} *)

let mk_intermediate_cfg cs =
  let g = CfgH.create () in
  let start, stop, succ = mic_create_vertices g cs in
  let labels = mic_hash_labels g in
  let r =
    { ProcedureH.cfg = g
    ; ProcedureH.start = start
    ; ProcedureH.stop = stop } in
  mic_add_edges r labels succ;
  r

(* helpers for [simplify_cfg] {{{ *)
let sc_interesting_label = function
  | C.Call_core _ | C.Assignment_core _ -> true
  | _ -> false

let sc_new_label = function
  | C.Assignment_core s ->
      failwith "INTERNAL: Assignments should already be turned into calls."
  | C.Call_core c -> G.Call_cfg c
  | C.Nop_stmt_core -> G.Nop_cfg
  | _ -> assert false

let sc_add_edges cfg nv s_cfg v =
  let add_outgoing v =
    let seen = HVHashtbl.create 1 in (* XXX: Switch to HashSet, functorial *)
    let rec add_to u =
      if not (HVHashtbl.mem seen u) then begin
        HVHashtbl.add seen u ();
        try G.Cfg.add_edge s_cfg v (HVHashtbl.find nv u)
        with Not_found -> CfgH.iter_succ add_to cfg u
      end in
    add_to in
  try CfgH.iter_succ (add_outgoing (HVHashtbl.find nv v)) cfg v
  with Not_found -> ()

(* }}} *)

let simplify_cfg { ProcedureH.cfg; start; stop } =
  let s_cfg = G.Cfg.create () in
  let nv = HVHashtbl.create 1 in (* old vertex -> new vertex *)
  let add_vertex v =
    let l = CfgH.V.label v in
    if v = start || v = stop || sc_interesting_label l then
      let w = G.Cfg.V.create (sc_new_label l) in
      G.Cfg.add_vertex s_cfg w; HVHashtbl.add nv v w in
  CfgH.iter_vertex add_vertex cfg;
  CfgH.iter_vertex (sc_add_edges cfg nv s_cfg) cfg;
  { G.Procedure.cfg = s_cfg
  ; start = HVHashtbl.find nv start
  ; stop = HVHashtbl.find nv stop }

let output_cfg n g =
  G.fileout_cfg (n ^ "_Cfg.dot") g

let output_cfgH n g =
  fileout_cfgH (n ^ "_CfgH.dot") g

let mk_cfg q =
  let n = q.C.proc_name in
  let g = option_map mk_intermediate_cfg q.C.proc_body in
  if !verbose >= 3 then maybe () (fun g -> output_cfgH n g.ProcedureH.cfg) g;
  let g = option_map simplify_cfg g in
  if !verbose >= 2 then maybe () (fun g -> output_cfg n g.G.Procedure.cfg) g;
  { q with C.proc_body = g }

(* helpers for [compute_call_graph] {{{ *)
module CallGraph = Digraph.Make
  (struct type t = G.Procedure.t C.procedure end)
  (Digraph.UnlabeledEdge)
module DotCg = Digraph.Dot (struct
  include CallGraph
  include Digraph.DotDefault
  let vertex_attributes v = [ `Label (CallGraph.V.label v).C.proc_name ]
end)
let output_cg = fileout DotCg.output_graph "callgraph.dot"

let ccg_add_edges cg von p =
  let u = Hashtbl.find von p.C.proc_name in
  let add_outgoing s = match G.Cfg.V.label s with
    | G.Call_cfg c ->
        (* NOTE: calls may bound only subset of all in/out arguments *)
        (try CallGraph.add_edge cg u (Hashtbl.find von c.C.call_name)
        with Not_found ->
          raise (Fatal ("undefined procedure: " ^ c.C.call_name)))
    | _ -> () in
  let pb b = G.Cfg.iter_vertex add_outgoing b.G.Procedure.cfg in
  maybe () pb p.C.proc_body

(* }}} *)

let compute_call_graph ps =
  let cg = CallGraph.create () in
  let von = Hashtbl.create 1 in (* procedure name -> vertex *)
  let add_vertex p =
    if Hashtbl.mem von p.C.proc_name then
      raise (Fatal ("repeated procedure name " ^ p.C.proc_name));
    Hashtbl.add von p.C.proc_name (CallGraph.V.create p) in
  List.iter add_vertex ps;
  List.iter (ccg_add_edges cg von) ps;
  if !verbose >= 2 then output_cg cg;
  cg

let output_sccs cs =
  let pp_procedure f v =
    let p = CallGraph.V.label v in
    fprintf f "@ %s" p.C.proc_name in
  let pp_component f ps = fprintf f "@[[%a ]@]@\n" (pp_list pp_procedure) ps in
  let file = open_out "sccs.txt" in
  let f = make_formatter (output file) (fun () -> flush file) in
  fprintf f "@[%a@]@?" (pp_list pp_component) cs;
  close_out file

(* Assumes that components come in reversed topological order. *)
let interpret_scc_dag cs =
  if !verbose >= 3 then output_sccs cs;
  failwith "TODO"

let interpret gs =
  let cg = compute_call_graph gs in
  let sccs =
    let module X = Digraph.Components.Make (CallGraph) in
    X.scc_list cg in
  interpret_scc_dag sccs

let main f =
  try
    let ps = parse f in
    let ps = desugar_assignments ps in
    let gs = List.map mk_cfg ps in
    interpret gs
  with Fatal m -> eprintf "@[ERROR: %s@." m

let args =
  [ "-v", Arg.Unit (fun () -> incr verbose), "increase verbosity" ]

(* TODO(rgrig): Allow multiple input files. *)
let _ =
  Arg.parse args main "alt_abd [options] <file>";
