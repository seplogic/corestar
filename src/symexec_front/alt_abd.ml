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
module HVHashtbl = Hashtbl.Make (CfgH.V)

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
    with Not_found -> failwith "bad cfg (TODO: nice user error)" in
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
  | C.Assignment_core s -> G.Assign_cfg s
  | C.Call_core (n, s) -> G.Call_cfg (n, s)
  | C.Nop_stmt_core -> G.Nop_cfg
  | _ -> assert false

let sc_add_edges cfg nv s_cfg v =
  let add_outgoing v =
    let seen = HVHashtbl.create 1 in
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
  let g = mk_intermediate_cfg q.C.proc_body in
  if !verbose >= 3 then output_cfgH n g.ProcedureH.cfg;
  let g = simplify_cfg g in
  if !verbose >= 2 then output_cfg n g.G.Procedure.cfg;
  { q with C.proc_body = g }

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
