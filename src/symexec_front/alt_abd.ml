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

let ast_to_inner_procedure { C.proc_name; proc_spec; proc_body } =
  let proc_spec = Core.ast_to_inner_spec proc_spec in
  let proc_body = option_map (List.map Core.ast_to_inner_core) proc_body in
  { C.proc_name; proc_spec; proc_body }

(* helpers for [mk_intermediate_cfg] {{{ *)
module CfgH = Digraph.Make
  (struct type t = C.inner_core end)
  (Digraph.UnlabeledEdge)
module HVHashtbl = Hashtbl.Make (CfgH.V)
module HVHashSet = HashSet.Make (CfgH.V)

module ProcedureH = G.MakeProcedure (CfgH)

let fileout f file_name g = G.fileout file_name (fun o -> f o g)

module DotH = Digraph.Dot (struct
  include Digraph.DotDefault (CfgH)
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
    let seen = HVHashSet.create 1 in
    let rec add_to u =
      if not (HVHashSet.mem seen u) then begin
        HVHashSet.add seen u;
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

(* POST: Only abstraction nodes have in-degree bigger than 1. *)
let insert_abstraction_nodes p =
  let module P = G.Procedure in let module H = G.CfgVHashtbl in
  let g = p.P.cfg in
  assert (G.Cfg.in_degree g p.P.start <= 1);
  let xs = H.create 1 in
  let record x = if G.Cfg.in_degree g x > 1 then begin
      assert (not (H.mem xs x));
      H.add xs x (G.Cfg.V.create G.Abs_cfg)
    end in
  let insert_abs z y =
    let replace x = G.Cfg.remove_edge g x z; G.Cfg.add_edge g x y in
    G.Cfg.iter_pred replace g z; G.Cfg.add_edge g y z in
  G.Cfg.iter_vertex record g; H.iter insert_abs xs

let output_cfg n g =
  G.fileout_cfg (n ^ "_Cfg.dot") g

let output_cfgH n g =
  fileout_cfgH (n ^ "_CfgH.dot") g

let mk_cfg q =
  let n = q.C.proc_name in
  let g = option_map mk_intermediate_cfg q.C.proc_body in
  if !verbose >= 3 then maybe () (fun g -> output_cfgH n g.ProcedureH.cfg) g;
  let g = option_map simplify_cfg g in
  ignore (option_map insert_abstraction_nodes g);
  if !verbose >= 2 then maybe () (fun g -> output_cfg n g.G.Procedure.cfg) g;
  { q with C.proc_body = g }

(* helpers for [compute_call_graph] {{{ *)
module CallGraph = Digraph.Make
  (struct type t = (G.Procedure.t, C.inner_spec) C.procedure end)
  (Digraph.UnlabeledEdge)
module DotCg = Digraph.Dot (struct
  include Digraph.DotDefault (CallGraph)
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
  cg, Hashtbl.find von

let output_sccs cs =
  let pp_procedure f v =
    let p = CallGraph.V.label v in
    fprintf f "@ %s" p.C.proc_name in
  let pp_component f ps = fprintf f "@[[%a ]@]@\n" (pp_list pp_procedure) ps in
  let file = open_out "sccs.txt" in
  let f = make_formatter (output file) (fun () -> flush file) in
  fprintf f "@[%a@]@?" (pp_list pp_component) cs;
  close_out file

(* symbolic execution for one procedure {{{ *)

module ProcedureInterpreter = struct

  type interpret_procedure_result =
    | NOK
    | OK
    | Spec_updated
    | Unknown

  (* Short names for Statement/Configuration Set/Dictionary *)
  module SS = G.CfgVHashSet
  module SD = G.CfgVHashtbl
  module CS = G.CVHashSet
  module CD = G.CVHashtbl

  (* Other short names. *)
  module CG = G.ConfigurationGraph

  let update _ =
    failwith "TODO"
    (* TODO: build set of old pre-configurations, build set of new pre-confs,
    for each new pre-conf find the post-conf and add it, simplify the new set
    of post-confs (if abstraction). *)

  (* Builds a graph of configurations, in BFS order. *)
  (* XXX: refactor; horrible now *)
  let interpret_cfg cfg v cs =
    let cg = CG.create () in
    let post_of = SD.create 1 in
    let statement_of = CD.create 1 in
    let cs = List.map CG.V.create cs in
    let cs_set = CS.of_list cs in
    List.iter (CG.add_vertex cg) cs;
    List.iter (fun c -> CD.add statement_of c v) cs;
    SD.add post_of v cs_set;
    let dirty_que, dirty_set = Queue.create (), SS.create 1 in
    let make_dirty v =
      if not (SS.mem dirty_set v) then begin
        SS.add dirty_set v; Queue.push v dirty_que
      end in
    G.Cfg.iter_succ make_dirty cfg v;
    let budget = ref (1 lsl 20) in
    while not (Queue.is_empty dirty_que) && !budget > 0 do begin
      decr budget;
      let v = Queue.pop dirty_que in SS.remove dirty_set v;
      if update cg cfg post_of statement_of v then
        G.Cfg.iter_succ make_dirty cfg v
    end done

  let interpret proc_of_name p =
    (* TODO: call interpret_cfg, abstract missing heaps, call again to check *)
    failwith "TODO"

end
(* }}} *)

(* Assumes that components come in reversed topological order. *)
let rec interpret_one_scc proc_of_name ps =
  let module PI = ProcedureInterpreter in
  let rs = List.map (PI.interpret proc_of_name) ps in
  if List.exists ((=) PI.Spec_updated) rs
  then interpret_one_scc proc_of_name ps
  else List.for_all ((=) PI.OK) rs

let interpret gs =
  let cg, von = compute_call_graph gs in
  let sccs =
    let module X = Digraph.Components.Make (CallGraph) in
    X.scc_list cg in
  if !verbose >= 3 then output_sccs sccs;
  let proc_of_name n = CallGraph.V.label (von n) in
  List.for_all (interpret_one_scc proc_of_name) sccs

let verify ps =
  let ps = desugar_assignments ps in
  let ps = List.map ast_to_inner_procedure ps in
  let gs = List.map mk_cfg ps in
  interpret gs

let procedures = ref []
let parse_file f = procedures =:: parse f

let args =
  [ "-v", Arg.Unit (fun () -> incr verbose), "increase verbosity" ]

let () =
  try
    procedures := [];
    Arg.parse args parse_file "alt_abd [options] <files>";
    if not (verify (List.concat !procedures)) then
      printf "@[verification failed@."
  with Fatal m -> eprintf "@[ERROR: %s@." m
