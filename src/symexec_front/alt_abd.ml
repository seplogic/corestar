(** Entry point for experiments on abduction with procedure calls. *)

open Format
module C = Core
module G = Cfg

let map_proc_body f x = { x with C.proc_body = f x.C.proc_body }

let parse fn =
  System.parse_file Parser.symb_question_file Lexer.token fn "core"

(* helpers for [mk_intermediate_cfg] {{{ *)
module CfgH = Graph.Imperative.Digraph.Abstract
  (struct type t = C.core_statement end)

module ProcedureH = G.MakeProcedure (CfgH)

module Display_CfgH = struct
  include G.Display_Cfg
  let vertex_attributes v = match CfgH.V.label v with
      C.Nop_stmt_core -> [`Label "NOP"]
    | C.Label_stmt_core s -> [`Label ("Label:" ^ s)]
    | C.Assignment_core _ -> [`Label "Assign "; `Shape `Box]
    | C.Call_core (fname, _) -> [`Label ("Call " ^ fname); `Shape `Box]
    | C.Goto_stmt_core ss -> [`Label ("Goto:" ^ (String.concat ", " ss))]
    | C.End -> [`Label "End"]
end
module Dot_CfgH = Graph.Graphviz.Dot(struct
  include Display_CfgH
  include CfgH
end)
module Dfs = Graph.Traverse.Dfs(CfgH)
let fprint_CfgH = Dot_CfgH.fprint_graph
let print_CfgH = fprint_CfgH std_formatter
let output_CfgH = Dot_CfgH.output_graph
let fileout_CfgH file_name g =
  G.fileout file_name (fun o -> output_CfgH o g)

let mic_create_vertices g cs =
  let succ = Hashtbl.create 13 in
  let cs = C.Nop_stmt_core :: cs @ [C.Nop_stmt_core] in
  let vs = List.map CfgH.V.create cs in
  List.iter (CfgH.add_vertex g) vs;
  Misc.iter_pairs (Hashtbl.add succ) vs;
  List.hd vs, List.hd (List.rev vs), succ

let mic_hash_labels g =
  let labels = Hashtbl.create 13 in
  let f v = match CfgH.V.label v with
    | C.Label_stmt_core l -> Hashtbl.add labels l v
    | _ -> () in
  CfgH.iter_vertex f g;
  labels

let mic_add_edges r labels succ =
  let g = r.ProcedureH.cfg in
  let vertex_of_label l =
    try Hashtbl.find labels l
    with Not_found -> failwith "bad cfg (todo: nice user error)" in
  let add_outgoing x = if x <> r.ProcedureH.stop then begin
      match CfgH.V.label x with
      | C.Goto_stmt_core ls ->
          List.iter (fun l -> CfgH.add_edge g x (vertex_of_label l)) ls
      | C.End -> CfgH.add_edge g x r.ProcedureH.stop
      | _  -> CfgH.add_edge g x (Hashtbl.find succ x)
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

let simplify_cfg {
    ProcedureH.cfg = g
  ; ProcedureH.start = start
  ; ProcedureH.stop = stop } =
  let sg = G.Cfg.create () in
  let representatives = Hashtbl.create 13 in
  let rep_builder rep () =
    let v_rep = G.Cfg.V.create rep in
    G.Cfg.add_vertex sg v_rep;
    v_rep in
  let find_rep v builder =
    try Hashtbl.find representatives v with Not_found ->
      let v_rep = builder () in Hashtbl.add representatives v v_rep; v_rep in
  let start_rep = rep_builder G.Nop_cfg () in
  Hashtbl.add representatives start start_rep;
  let work_set = WorkSet.singleton (start, start_rep) in
  let interest sv = match CfgH.V.label sv with
      C.Nop_stmt_core when sv = start || sv = stop -> Some G.Nop_cfg
    | C.Call_core (fname, call) -> Some (G.Call_cfg (fname, call))
    | _ -> None in
  let rec process_successor new_interest v_rep visited sv = match interest sv with
      Some i ->
	let sv_rep = find_rep sv (rep_builder i) in
	  G.Cfg.add_edge sg v_rep sv_rep;
	  new_interest (sv, sv_rep)
    | None ->
	if HashSet.mem visited sv then ()
	else (
	  HashSet.add visited sv;
	  CfgH.iter_succ (process_successor new_interest v_rep visited) g sv
	) in
  let add_successors new_interest (v, v_rep) =
    let visited = HashSet.singleton v in
    CfgH.iter_succ (process_successor new_interest v_rep visited) g v in
  WorkSet.perform_work work_set add_successors;
  sg

let mk_cfg cs =
  let g = mk_intermediate_cfg cs in
  simplify_cfg g

let compute_call_graph _ = failwith "todo"

let compute_scc_dag _ = failwith "todo"

let interpret_scc_dag _ = failwith "todo" (* interpret in postorder *)

let interpret gs =
  let cg = compute_call_graph gs in
  let scc_dag = compute_scc_dag cg in
  interpret_scc_dag scc_dag

let print_Cfg { C.proc_name=n; C.proc_spec=_; C.proc_body=g } =
  printf "@[Graph for %s:@\n" n;
  G.print_Cfg g;
  printf "@]@."
(*  printf "@[Graph for %s:@\n@a@." n G.fprint_Cfg g *)

let output_Cfg { C.proc_name=n; C.proc_spec=_; C.proc_body=g } =
  G.fileout_Cfg (n ^ "_Cfg.dot") g

let output_CfgH { C.proc_name=n; C.proc_spec=_; C.proc_body=g } =
  fileout_CfgH (n ^ "_CfgH.dot") g.ProcedureH.cfg

let main f =
  let ps = parse f in

  (* TODO: skip next two, and move printing in mk_cfg. *)
  let igs = List.map (map_proc_body mk_intermediate_cfg) ps in
  List.iter output_CfgH igs;

  let gs = List.map (map_proc_body mk_cfg) ps in
  List.iter output_Cfg gs;
  interpret gs

let _ =
  Arg.parse [] main "alt_abd <file>";
