(** Entry point for experiments on abduction with procedure calls. *)

open Debug
open Format
module C = Core
module G = Cfg

let verbose = ref 0

let map_proc_body f x = { x with C.proc_body = f x.C.proc_body }

let parse fn =
  System.parse_file Parser.symb_question_file Lexer.token fn "core"

(* helpers for [mk_intermediate_cfg] {{{ *)
module CfgH = Digraph.Make
  (struct type t = C.core_statement end)
  (struct type t = unit let compare = compare let default = () end)

module ProcedureH = G.MakeProcedure (CfgH)

module DotH = Digraph.Dot (struct
  include CfgH
  include Digraph.DotDefault
  let vertex_attributes v = match CfgH.V.label v with
      C.Nop_stmt_core -> [`Label "NOP"]
    | C.Label_stmt_core s -> [`Label ("Label:" ^ s)]
    | C.Assignment_core _ -> [`Label "Assign "; `Shape `Box]
    | C.Call_core (fname, _) -> [`Label ("Call " ^ fname); `Shape `Box]
    | C.Goto_stmt_core ss -> [`Label ("Goto:" ^ (String.concat "," ss))]
    | C.End -> [`Label "End"]
end)
let fileout_cfgH file_name g =
  G.fileout file_name (fun o -> DotH.output_graph o g)

let mic_create_vertices g cs =
  let succ = Hashtbl.create 1 in
  let cs = C.Nop_stmt_core :: cs @ [C.Nop_stmt_core] in
  let vs = List.map CfgH.V.create cs in
  List.iter (CfgH.add_vertex g) vs;
  Misc.iter_pairs (Hashtbl.add succ) vs;
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
    with Not_found -> failwith "bad cfg (todo: nice user error)" in
  let add_outgoing x = if not (CfgH.V.equal x r.ProcedureH.stop) then begin
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

(* TODO(rgrig): This function is *way* too long. *)
let simplify_cfg
  { ProcedureH.cfg = g
  ; ProcedureH.start = start
  ; ProcedureH.stop = stop }
=
  let sg = G.Cfg.create () in
  let representatives = Hashtbl.create 1 in
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

let output_cfg n g =
  G.fileout_cfg (n ^ "_Cfg.dot") g

let output_cfgH n g =
  fileout_cfgH (n ^ "_CfgH.dot") g

let mk_cfg q =
  let n = q.C.proc_name in
  let g = mk_intermediate_cfg q.C.proc_body in
  if !verbose >= 3 then output_cfgH n g.ProcedureH.cfg;
  let g = simplify_cfg g in
  if !verbose >= 2 then output_cfg n g;
  { q with C.proc_body = g } (* XXX(rgrig): g should be C.Procedure. *)

let compute_call_graph _ = failwith "todo"

let compute_scc_dag _ = failwith "todo"

let interpret_scc_dag _ = failwith "todo" (* interpret in postorder *)

let interpret gs =
  let cg = compute_call_graph gs in
  let scc_dag = compute_scc_dag cg in
  interpret_scc_dag scc_dag

let main f =
  let ps = parse f in
  let gs = List.map mk_cfg ps in
  interpret gs

let args =
  [ "-v", Arg.Unit (fun () -> incr verbose), "increase verbosity" ]

(* TODO(rgrig): Allow multiple input files. *)
let _ =
  Arg.parse args main "alt_abd [options] <file>";
