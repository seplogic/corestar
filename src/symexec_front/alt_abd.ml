(** Entry point for experiments on abduction with procedure calls. *)

open Corestar_std
open Debug
open Format

module C = Core
module G = Cfg
module P = Cfg.Procedure
module PS = Psyntax

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
  { P.cfg = s_cfg
  ; start = HVHashtbl.find nv start
  ; stop = HVHashtbl.find nv stop }

(* POST: Only abstraction nodes have in-degree bigger than 1. *)
let insert_abstraction_nodes p =
  let module H = G.CfgVHashtbl in
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
  if !verbose >= 3 then option () (fun g -> output_cfgH n g.ProcedureH.cfg) g;
  let g = option_map simplify_cfg g in
  ignore (option_map insert_abstraction_nodes g);
  if !verbose >= 2 then option () (fun g -> output_cfg n g.P.cfg) g;
  { q with C.proc_body = g }

(* helpers for [compute_call_graph] {{{ *)
module CallGraph = Digraph.Make
  (struct type t = (P.t, C.inner_spec) C.procedure end)
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
  let pb b = G.Cfg.iter_vertex add_outgoing b.P.cfg in
  option () pb p.C.proc_body

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
  let pp_procedure f p = fprintf f "@ %s" p.C.proc_name in
  let pp_component f ps = fprintf f "@[[%a ]@]@\n" (pp_list pp_procedure) ps in
  let file = open_out "sccs.txt" in
  let f = make_formatter (output file) (fun () -> flush file) in
  fprintf f "@[%a@]@?" (pp_list pp_component) cs;
  close_out file

(* symbolic execution for one procedure {{{ *)
module ProcedureInterpreter : sig
  type interpret_procedure_result =
    | NOK
    | OK
    | Spec_updated
    | Unknown
  val interpret
    : (string -> CallGraph.V.label) -> CallGraph.V.label -> interpret_procedure_result
end = struct

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

  type interpreter_context =
    { confgraph : CG.t
    ; flowgraph : G.Cfg.t (* input, unchanged *)
    ; post_of : CS.t SD.t (* maps a statement to its post-configurations *)
    ; pre_of : CS.t SD.t  (* maps a statement to its pre-configurations *)
    ; statement_of : G.Cfg.vertex CD.t (* inverse of [post_of] *) }
  (* INV: The set [pre_of s] should never shrink, for all statements [s]. *)
  (* NOTE: Be careful, these are imperative data structures. *)

  (* Executing one statement produces one [choice_tree], which is later
  integrated into the confgraph by [update]. (Alternatively, the function
  [execute] could know abouf confgraphs, rather than being just a local
  operation.) *)
  type choice_tree =
    | CT_error
    | CT_ok of G.ok_configuration
    | CT_split of G.split_type * choice_tree list

  let confs d s = try SD.find d s with Not_found -> CS.create 1
  let post_confs context = confs context.post_of
  let pre_confs context = confs context.pre_of

  let remove_conf context c =
    let s = CD.find context.statement_of c in
    CS.remove (post_confs context s) c;
    let f t = CS.remove (pre_confs context t) c in
    G.Cfg.iter_succ f context.flowgraph s;
    CG.remove_vertex context.confgraph c

  let conf_of_vertex v = match CG.V.label v with
    | G.OkConf (c, _) -> c
    | G.ErrorConf -> assert false

  let make_angelic c = G.OkConf (c, G.Angelic)
  let make_demonic c = G.OkConf (c, G.Demonic)

  let make_angelic_choice = function
    | [] -> CT_error
    | [c] -> c
    | cs -> CT_split (G.Angelic, cs)

  let make_demonic_choice = function
    | [] -> failwith "INTERNAL: empty demonic choice"
    | [c] -> c
    | cs -> CT_split (G.Demonic, cs)

  (* Updates the [pre_of s] by adding new confs, and returns what is added. *)
  let update_pre_confs context s =
    let old_pre = pre_confs context s in
    let new_pre = CS.create 1 in
    let add_new_pre c = if not (CS.mem old_pre c) then CS.add new_pre c in
    let add_posts_of s = CS.iter add_new_pre (post_confs context s) in
    G.Cfg.iter_pred add_posts_of context.flowgraph s;
    CS.iter (CS.add old_pre) new_pre;
    SD.replace context.pre_of s old_pre;
    new_pre

  (* Helper for [update_post_confs]. *)
  let update_post_confs_execute execute context sv posts pv =
    let new_post q =
      let qv = CG.V.create q in
      CS.add posts qv; CD.add context.statement_of qv sv;
      qv in
    let rec graph_of_tree parent =
      let add_child = CG.add_edge context.confgraph parent in
      let ok_vertex t = G.OkConf (conf_of_vertex parent, t) in
      function
        | CT_error -> add_child (new_post G.ErrorConf)
        | CT_ok c -> add_child (new_post (ok_vertex G.Demonic))
        | CT_split (t, qs) ->
            let child = CG.V.create (ok_vertex t) in add_child child;
            List.iter (graph_of_tree child) qs in
    execute (conf_of_vertex pv) (G.Cfg.V.label sv) |> graph_of_tree pv

  (* Update [post_of sv]. For each pre-conf in [pvs], it executes
  symbolically the statement [sv], using the helper [update_post_confs_execute].
  Thet it calls [abstract] on the whole set of cost-confs. The [confgraph] is
  updated. *)
  let update_post_confs execute abstract context pvs sv =
    let posts = post_confs context sv in
    CS.iter (update_post_confs_execute execute context sv posts) pvs;
    let posts = abstract context.confgraph posts in
    SD.replace context.post_of sv posts

  let update execute abstract context s =
    let new_pre = update_pre_confs context s in
    update_post_confs execute abstract context new_pre s;
    CS.length new_pre > 0

  let emp = Specification.empty_inner_form

  let initialize procedure pre =
    let confgraph = CG.create () in
    let flowgraph = procedure.P.cfg in
    let post_of = SD.create 1 in
    let pre_of = SD.create 1 in
    let statement_of = CD.create 1 in
    let conf = CG.V.create
      (G.OkConf ({ G.current_heap = pre; missing_heap = emp }, G.Demonic)) in
    CG.add_vertex confgraph conf;
    CD.add statement_of conf procedure.P.start;
    SD.add post_of procedure.P.start (CS.singleton conf);
    { confgraph; flowgraph; post_of; pre_of; statement_of }

  module StatementBfs = Bfs.Make (SS)
  module ConfBfs = Bfs.Make (CS)

  let make_nonempty = function
    | [] -> [(emp, emp)]
    | xs -> xs

  let abduct logic p q =
    Sepprover.abduct_inner logic p q |> option_map make_nonempty

  let frame logic p q =
    Sepprover.frame_inner logic p q
    |> option_map (List.map (fun x -> (emp, x)))
    |> option_map make_nonempty

  let substitute_list var =
    let gen = let x = ref 0 in fun () -> incr x; var !x in
    let sub = Sepprover.update_var_to (gen ()) in
    List.fold_right sub

  let substitute_args = substitute_list SpecOp.parameter_var
  let substitute_rets = substitute_list SpecOp.return_var

  let collect_assignables fg =
    let f v acc = match G.Cfg.V.label v with
      | G.Abs_cfg | G.Nop_cfg -> acc
      | G.Call_cfg c -> List.fold_right PS.vs_add c.C.call_rets acc in
    G.Cfg.fold_vertex f fg PS.vs_empty

  (* Used as the [make_framable] argument of the generic [execute]. *)
  let replace_assignables =
    let replace_one v f =
      match Sepprover.get_equals_pvar_free v f with
      | [] -> Sepprover.kill_var v f
      | t :: _ -> Sepprover.update_var_to v t f in
    PS.vs_fold replace_one

  (* The prover answers a query H⊢P with a list F1⊢A1, ..., Fn⊢An of assumptions
  that are sufficient.  This implies that H*(A1∧...∧An)⊢P*(F1∨...∨Fn).  It is
  sufficient to demonically split on the frames Fk, and then angelically on the
  antiframes Ak.  Further, it is sufficient to demonically split on (antiframe,
  frame) pairs (Ak, Fk). *)
  let execute_one_triple
      abduct make_framable pre_conf args rets { Spec.pre; post }
  =
    let pre = substitute_args args pre in
    let post = substitute_args args (substitute_rets rets post) in
    let afs = abduct pre_conf.G.current_heap pre in
    assert (afs <> Some []);
    let branch afs =
      let mk_post_conf (a, f) =
        let ( * ) = Sepprover.conjoin_inner in
        CT_ok
          { G.missing_heap = pre_conf.G.missing_heap * make_framable a
          ; current_heap = post * f } in
      afs |> List.map mk_post_conf |> make_demonic_choice in
    option CT_error branch afs

  (* XXX: Add check for postcondition. *)
  let execute abduct make_framable =
    let execute_one_triple = execute_one_triple abduct make_framable in
    fun spec_of pre_conf -> function
    | G.Call_cfg { C.call_rets; call_name; call_args } ->
        let call_rets = List.map (fun v -> PS.Arg_var v) call_rets in
        spec_of call_name |> HashSet.elements
          |> List.map (execute_one_triple pre_conf call_args call_rets)
          |> make_angelic_choice
    | G.Abs_cfg | G.Nop_cfg -> CT_ok pre_conf

  let abstract context confs = confs (* XXX *)

  (* helpers for [prune_error_confs] {{{ *)

  let pec_init context ne_succ_cnt q v = match CG.V.label v with
    | G.ErrorConf -> ConfBfs.enque q v
    | G.OkConf (_, G.Angelic) ->
        let f v = match CG.V.label v with G.ErrorConf -> 0 | _ -> 1 in
        let cnt = CG.fold_succ (fun v n -> f v + n) context.confgraph v 0 in
        CD.add ne_succ_cnt v cnt
    | _ -> ()

  let pec_process context ne_succ_cnt q =
    let process_pred u =
      if not (ConfBfs.is_seen q u) then begin
        match CG.V.label u with
          | G.OkConf (_, G.Angelic) ->
              let n = CD.find ne_succ_cnt u - 1 in
              CD.replace ne_succ_cnt u n;
              assert (n >= 0);
              if n = 0 then ConfBfs.enque q u
          | G.OkConf (_, G.Demonic) -> ConfBfs.enque q u
          | G.ErrorConf -> failwith "ErrorConf has no successors"
      end in
    CG.iter_pred process_pred context.confgraph

  (* }}} *)

  let prune_error_confs context =
    let ne_succ_cnt = CD.create 1 in (* counts non-error angelic successors *)
    let q = ConfBfs.initialize true in
    CG.iter_vertex (pec_init context ne_succ_cnt q) context.confgraph;
    while not (ConfBfs.is_done q) do
      pec_process context ne_succ_cnt q (ConfBfs.deque q)
    done;
    List.iter (remove_conf context) (ConfBfs.get_seen q)

  (* Builds a graph of configurations, in BFS order. *)
  let interpret_flowgraph update procedure pre =
    let context = initialize procedure pre in
    let q = StatementBfs.initialize false in
    let enque_succ = G.Cfg.iter_succ (StatementBfs.enque q) context.flowgraph in
    enque_succ procedure.P.start;
    let rec bfs budget =
      if budget = 0 || StatementBfs.is_done q then budget else begin
        let s = StatementBfs.deque q in
        if update context s then enque_succ s;
        bfs (budget - 1)
      end in
    if bfs (1 lsl 20) = 0 then None
    else Some (prune_error_confs context; post_confs context procedure.P.stop)

  let update_infer proc_of_name body =
    let abduct = abduct Psyntax.empty_logic in (* XXX: load rules *)
    let assignables = collect_assignables body.P.cfg in
    let make_framable = replace_assignables assignables in
    let spec_of n = (proc_of_name n).C.proc_spec in
    let execute = execute abduct make_framable spec_of in
    update execute abstract

  let update_check proc_of_name =
    let abduct = frame Psyntax.empty_logic in (* XXX: load rules *)
    let check_emp x = assert (x = emp); emp in
    let spec_of n = (proc_of_name n).C.proc_spec in
    let execute = execute abduct check_emp spec_of in
    update execute abstract

  let interpret proc_of_name p = match p.C.proc_body with
    | None -> OK
    | Some body ->
        let process_triple triple =
          let inferred =
            interpret_flowgraph (update_infer proc_of_name body) body triple in
          failwith "TODO" in
        (* TODO: call interpret_cfg, abstract missing heaps, call again to check *)
        (* TODO: add assertion at the end of p, for checking the postcondition *)
        failwith "TODO a";
        NOK

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
  let sccs = List.map (List.map CallGraph.V.label) sccs in
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
