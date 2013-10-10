(** Symbolic execution (with and without spec inference) happens here. *)
(* modules, constants *) (* {{{ *)
open Corestar_std
open Debug
open Format

module C = Core
module Expr = Expression
module G = Cfg
module P = Cfg.Procedure

exception Fatal of string

let bfs_limit = 1 lsl 20
(* }}} *)
(* helpers for substitutions *) (* {{{ *)

let substitute_list var ts e =
  let p i t = (var i, t) in
  Expr.substitute (ListH.mapi p ts) e

let substitute_args = substitute_list CoreOps.parameter
let substitute_rets = substitute_list CoreOps.return

let specialize_spec rets args xs =
  let ret_terms = List.map (fun v -> Expr.mk_var v) rets in
  let f { Core.pre; post; modifies } =
    { Core.pre = substitute_args args pre
    ; post = substitute_args args (substitute_rets ret_terms post)
    ; modifies = lift_option2 (@) modifies (Some rets) } in
  xs |> C.TripleSet.elements |> List.map f |> C.TripleSet.of_list

(* }}} *)
(* graph operations *) (* {{{ *)
(* helpers for [mk_intermediate_cfg] {{{ *)
module CfgH = Digraph.Make
  (struct type t = C.statement end)
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
  | C.Assignment_core { C.asgn_rets; asgn_args; asgn_spec } ->
      G.Spec_cfg (specialize_spec asgn_rets asgn_args asgn_spec)
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
  if !Config.verbosity >= 3 then
    option () (fun g -> output_cfgH n g.ProcedureH.cfg) g;
  let g = option_map simplify_cfg g in
  ignore (option_map insert_abstraction_nodes g);
  if !Config.verbosity >= 2 then
    option () (fun g -> output_cfg n g.P.cfg) g;
  { q with C.proc_body = g }

(* helpers for [compute_call_graph] {{{ *)
module CallGraph = Digraph.Make
  (struct type t = P.t C.procedure end)
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
    let v = CallGraph.V.create p in
    Hashtbl.add von p.C.proc_name v;
    CallGraph.add_vertex cg v in
  List.iter add_vertex ps;
  List.iter (ccg_add_edges cg von) ps;
  if !Config.verbosity >= 2 then output_cg cg;
  cg, Hashtbl.find von

let output_sccs cs =
  let pp_procedure f p = fprintf f "@ %s" p.C.proc_name in
  let pp_component f ps = fprintf f "@[[%a ]@]@\n" (pp_list pp_procedure) ps in
  let file = open_out "sccs.txt" in
  let f = make_formatter (output file) (fun () -> flush file) in
  fprintf f "@[%a@]@?" (pp_list pp_component) cs;
  close_out file

(* }}} *)
(* symbolic execution for one procedure {{{ *)
module ProcedureInterpreter : sig
  type interpret_procedure_result =
    | NOK
    | OK
    | Spec_updated
    | Unknown
  val interpret
    : (string -> CallGraph.V.label)
      -> C.rules
      -> bool
      -> CallGraph.V.label
      -> interpret_procedure_result
end = struct

  type interpret_procedure_result =
    | NOK
    | OK
    | Spec_updated
    | Unknown  (* timeout *)

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

  let pp_context f c =
    let pp_vertex v = fprintf f "@ @[%a@]" Cfg.pp_configuration (CG.V.label v) in
    fprintf f "@[<2>Configuration graph:";
    CG.iter_vertex pp_vertex c.confgraph;
    fprintf f "@]@,@?";

  (* Executing one statement produces one [choice_tree], which is later
  integrated into the confgraph by [update]. (Alternatively, the function
  [execute] could know about confgraphs, rather than being just a local
  operation.) *)
  type choice_tree =
    | CT_error
    | CT_ok of G.ok_configuration
    | CT_split of G.split_type * choice_tree list

  let confs d s = try SD.find d s with Not_found -> CS.create 1
  let post_confs context = confs context.post_of
  let pre_confs context = confs context.pre_of

  let remove_conf context c =
    begin try
      let s = CD.find context.statement_of c in
      CS.remove (post_confs context s) c;
     let f t = CS.remove (pre_confs context t) c in
     G.Cfg.iter_succ f context.flowgraph s
    with Not_found -> () end; (* [c] was intermediate, not attached to statements *)
    CG.remove_vertex context.confgraph c

  let conf_of_vertex v = match CG.V.label v with
    | G.OkConf (c, _) -> c
    | G.ErrorConf -> assert false

  let make_angelic c = G.OkConf (c, G.Angelic)
  let make_demonic c = G.OkConf (c, G.Demonic)

  let is_ok_conf_vertex v = match CG.V.label v with
    | G.OkConf _ -> true
    | _ -> false

  let make_angelic_choice = function
    | [] -> CT_error
    | [c] -> c
    | cs -> CT_split (G.Angelic, cs)

  let make_demonic_choice = function
    | [c] -> c
    | cs -> CT_split (G.Demonic, cs)

  (* Updates the [pre_of s] by adding new confs, and returns what is added. *)
  let update_pre_confs context s =
    let old_pre = pre_confs context s in
    let new_pre = CS.create 1 in
    let add_new_pre c =
      if is_ok_conf_vertex c && not (CS.mem old_pre c) then CS.add new_pre c in
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
        | CT_ok c -> add_child (new_post (G.OkConf (c, G.Demonic)))
        | CT_split (t, qs) ->
            let child = CG.V.create (ok_vertex t) in add_child child;
            List.iter (graph_of_tree child) qs in
    execute (conf_of_vertex pv) sv |> graph_of_tree pv

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

  let initialize procedure pre =
    let confgraph = CG.create () in
    let flowgraph = procedure.P.cfg in
    let post_of = SD.create 1 in
    let pre_of = SD.create 1 in
    let statement_of = CD.create 1 in
    let conf = CG.V.create
      (G.OkConf ({ G.current_heap = pre; missing_heap = Expr.emp }, G.Demonic)) in
    CG.add_vertex confgraph conf;
    CD.add statement_of conf procedure.P.start;
    SD.add post_of procedure.P.start (CS.singleton conf);
    { confgraph; flowgraph; post_of; pre_of; statement_of }

  module StatementBfs = Bfs.Make (SS)
  module ConfBfs = Bfs.Make (CS)

  let make_nonempty = function
    | [] -> [(Expr.emp, Expr.emp)]
    | xs -> xs

  let abduct = Prover.biabduct

  let frame calculus p q =
    Prover.infer_frame calculus p q
    |> List.map (fun x -> { Prover.antiframe = x; frame = Expr.emp })

  let collect_pvars fg =
    let cp_vertex v acc = match G.Cfg.V.label v with
      | G.Abs_cfg | G.Nop_cfg -> acc
      | G.Call_cfg { C.call_rets; call_name; call_args } ->
          failwith "INTERNAL: calls should be removed by [inline_call_specs]"
      | G.Spec_cfg spec ->
          let cp_triple { Core.pre; post } acc =
            let cp_formula f =
              let vs = List.filter Expr.is_pvar (Expr.vars f) in
              List.fold_right StringSet.add vs in
            acc |> cp_formula pre |> cp_formula post in
          C.TripleSet.fold cp_triple spec acc
    in
    StringSet.elements (G.Cfg.fold_vertex cp_vertex fg StringSet.empty)

  (* Process [g] such that it doesn't contain any of the variables in [vs].
  If a variable [v] is in [vs], then it must be substituted by some
  expression [e] that contains no variable from [pvars].  As a last resort, [e]
  is set to be a fresh logical variable. But first, we check whether [f]
  contains a conjunct [v=e], where [e] has the desired property. *)
  let kill_pvars_with vs f g =
    let h = StringHash.create (List.length vs) in
    List.iter (fun v -> StringHash.add h v None) vs;
    let is_pvar = StringHash.mem h in
    let is_pvar_expr = Expr.cases is_pvar (fun _ _ -> false) in
    let rec is_pvar_free e =
      let app _ xs = List.for_all is_pvar_free xs in
      Expr.cases (not @@ is_pvar) app e in
    let pick_better e1 e2 =
      let size = function
        | None -> max_int
        | Some e -> if is_pvar_free e then Expr.size e else max_int in
      if size e1 < size e2 then e1 else e2 in
    let rec find_bindings e =
      let eq e1 e2 =
        let b1, b2 = is_pvar_expr e1, is_pvar_expr e2 in
        if b1 || b2 then
          let v, e = if b1 then e1, e2 else e2, e1 in
          let v = Expr.bk_var v in
          let old_e = StringHash.find h v in
          StringHash.replace h v (pick_better (Some e) old_e) in
      let app =
        Expr.on_star (List.iter find_bindings)
        & Expr.on_eq eq
        & (fun _ _ -> ()) in
      Expr.cases (fun _ -> ()) app e in
    let extract_binding v e bs =
      let e = match e with None -> Expr.mk_var (Expr.freshen v) | Some e -> e in
      (v, e) :: bs in
    let bs = StringHash.fold extract_binding h [] in
    Expr.substitute bs g

  let kill_pvars vs = kill_pvars_with vs Expr.emp

  (* The prover answers a query H⊢P with a list F1⊢A1, ..., Fn⊢An of assumptions
  that are sufficient.  This implies that H*(A1∧...∧An)⊢P*(F1∨...∨Fn).  It is
  sufficient to demonically split on the frames Fk, and then angelically on the
  antiframes Ak.  Further, it is sufficient to demonically split on (antiframe,
  frame) pairs (Ak, Fk). *)
  let execute_one_triple
      abduct is_deadend make_framable
      pre_conf ({ Core.pre; post; modifies } as triple)
  =
    if log log_exec then
      fprintf logf "@[<2>execute %a@ from %a@ to get@\n"
        CoreOps.pp_triple triple
        Cfg.pp_ok_configuration pre_conf;
    let vs = match modifies with
      (* TODO: ensure None doesn't happen (assert?poly?), and expand before *)
      | None -> List.filter Expr.is_pvar (Expr.vars post)
      | Some vs -> vs in
    let afs = abduct pre_conf.G.current_heap pre in
    let branch afs =
      let mk_post_conf { Prover.antiframe = a; frame = f } =
        let ( * ) = Expr.mk_star in
        let conf =
          { G.missing_heap
            = pre_conf.G.missing_heap * make_framable pre_conf.G.current_heap a
          ; current_heap = post * kill_pvars vs f } in
        if log log_exec then
          fprintf logf "@,%a" Cfg.pp_ok_configuration conf;
        conf in
      let mk_ok conf = CT_ok conf in
      let keep_conf { G.missing_heap; current_heap } =
        not (is_deadend missing_heap) && not (is_deadend current_heap) in
      afs
        |> List.map mk_post_conf
        |> List.filter keep_conf
        |> List.map mk_ok
        |> make_demonic_choice in
    let r = match afs with
      | [] ->
          if log log_exec then
            fprintf logf "(error conf)";
          CT_error
      | afs -> branch afs in
    if log log_exec then fprintf logf "@]@,@?";
    r

  let execute abduct is_deadend make_framable =
    let execute_one_triple =
      execute_one_triple abduct is_deadend make_framable in
    fun spec_of pre_conf statement ->
      statement
      |> spec_of
      |> C.TripleSet.elements
      |> List.map (execute_one_triple pre_conf)
      |> make_angelic_choice

  type ('x, 'xs) abs_collection =
    { ac_fold : 'acc. ('x -> 'acc -> 'acc) -> 'xs -> 'acc -> 'acc
    ; ac_add : 'x -> 'xs -> 'xs
    ; ac_mk : unit -> 'xs }

  let abstract ac add_edge implies confs =
    let add_edges l c = List.iter (flip add_edge c) l in
    let partition add_ns (ys, ns) p xs =
      let f x (ys, ns) =
        if p x then (x :: ys, ns) else (ys, add_ns x ns) in
      ac.ac_fold f xs (ys, ns) in
    let find p xs = fst (partition (fun _ _ -> ()) ([], ()) p xs) in

    let f c weakest = (* Warning x^2 *)
      let c_implies = find (implies c) weakest in (* c=> c_implies *)
      match c_implies with
	| [] ->
	  begin (* c needs to be added *)
	    let implies_c, not_implies_c = (* ∀x in implies_c: x => c *)
              partition ac.ac_add ([], ac.ac_mk ()) (flip implies c) weakest in
            add_edges implies_c c;
            ac.ac_add c not_implies_c
	  end
        | r :: _ -> add_edge c r; weakest in
    ac.ac_fold f confs (ac.ac_mk ())

  let implies_conf logic v1 v2 = match CG.V.label v1, CG.V.label v2 with
    | G.ErrorConf, G.ErrorConf -> true
    | G.ErrorConf, _ | _, G.ErrorConf -> false
    | G.OkConf (c1, _), G.OkConf (c2, _) ->
        failwith "TODO Symexec.implies_conf"
(*
      Sepprover.implies logic c1.G.current_heap c2.G.current_heap &&
      Sepprover.implies logic c2.G.missing_heap c1.G.missing_heap
*)

  let implies_triple logic t1 t2 = failwith "TODO Symexec.implies_triple"
(*
    Sepprover.implies logic t1.C.post t2.C.post &&
    Sepprover.implies logic t2.C.pre t1.C.pre
*)

  (* The notation "weakest" and "implies" refer only to the current heap.
     For ok_configurations (M1, H1) and (M2, H2), we observe that

     [[(M1, H1)]] /\ M2 => M1 /\ H1 => H2
     ------------------------------------
             [[(M2, H2)]]

     where [[(M, H)]] is roughly that "if M is added to the preconditon, then H will be true of the current heap".

     In this sense, implies (M1, H1) (M2, H2) actually checks
     [[(M2, H2)]] => [[(M1, H1)]]. *)
  let abstract_conf logic confgraph =
    abstract
      { ac_fold = CS.fold
      ; ac_add = (fun x xs -> CS.add xs x; xs)
      ; ac_mk = (fun () -> CS.create 0) }
      (CG.add_edge confgraph) (implies_conf logic)
  let abstract_triple logic =
    abstract
      { ac_fold = List.fold_right
      ; ac_add = (fun x xs -> x :: xs)
      ; ac_mk = (fun () -> []) }
      (fun _ _ -> ()) (implies_triple logic)

  (* helpers for [prune_error_confs] {{{ *)

  let pec_init context ne_succ_cnt q v = match CG.V.label v with
    | G.ErrorConf -> ConfBfs.enque q v
    | G.OkConf (_, G.Angelic) ->
        (* TODO(rgrig): simplify? *)
        let cnt = CG.fold_succ (fun _ -> succ) context.confgraph v 0 in
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
          | G.ErrorConf -> failwith "ErrorConf should have no successors"
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

  let get_new_specs context stop =
    prune_error_confs context;
    post_confs context stop |> CS.elements |> List.map conf_of_vertex

  let output_confgraph n g =
    G.fileout_confgraph (n ^ "_confgraph.dot") g

  let confgraph_counter = ref 0
  let output_confgraph_i n i g =
    if !confgraph_counter < 1000 then begin
      let ccc = incr confgraph_counter; !confgraph_counter in
      let fname = sprintf "%s_confgraph_%05d_%d.dot" n ccc i in
      if log log_exec then fprintf logf "@[Outputing confgraph to file: %s@]@\n@?" fname;
      G.fileout_confgraph fname g
    end

  (* Builds a graph of configurations, in BFS order. *)
  let interpret_flowgraph proc_name update procedure pre =
    let context = initialize procedure pre in
    let q = StatementBfs.initialize false in
    let enque_succ = G.Cfg.iter_succ (StatementBfs.enque q) context.flowgraph in
    enque_succ procedure.P.start;
    let rec bfs budget =
      if log log_exec then output_confgraph_i proc_name budget context.confgraph;
      if budget = 0 || StatementBfs.is_done q then budget else begin
        let s = StatementBfs.deque q in
        if update context s then enque_succ s;
        bfs (budget - 1)
      end in
    if bfs bfs_limit = 0 then begin
      if log log_exec then fprintf logf "@[interpret_flowgraph limit reached@]@?";
      None
    end
    else begin
(*      if log log_exec then output_confgraph proc_name context.confgraph; *)
      Some (get_new_specs context procedure.P.stop)
    end

  let empty_triple = { Core.pre = Expr.emp; post = Expr.emp; modifies = Some [] }

  let spec_of post =
    let post = CoreOps.mk_assert post in
    let nop = C.TripleSet.singleton empty_triple in
    fun stop statement ->
    if statement = stop
    then begin assert (G.Cfg.V.label statement = G.Nop_cfg); post end
    else begin match G.Cfg.V.label statement with
      | G.Abs_cfg | G.Nop_cfg -> nop
      | G.Spec_cfg s -> s
      | G.Call_cfg { C.call_rets; call_name; call_args } ->
          assert false (* should have called [inline_call_specs] before *)
    end

  let update_infer pvars rules body post =
    let abduct = abduct rules.C.calculus in
    let is_deadend e = Prover.is_entailment rules.C.calculus e Expr.fls in
    let make_framable = kill_pvars_with pvars in
    let execute =
      execute abduct is_deadend make_framable (spec_of post body.P.stop) in
    update execute (abstract_conf rules)

  let update_check rules body post =
    let abduct = frame rules in
    let is_deadend = failwith "TODO Symexec.update_check" in
(*     let is_deadend = Sepprover.inconsistent rules in *)
    let check_emp _ x = assert (x = Expr.emp); Expr.emp in
    let execute =
      execute abduct is_deadend check_emp (spec_of post body.P.stop) in
    update execute (abstract_conf rules)

  (* Lifts binary operators to options, *but* treats [None] as the identity. *)
  let bin_option f x y = match x, y with
    | None, x | x, None -> x
    | Some x, Some y -> Some (f x y)

  let lol_cat xs = List.fold_left (bin_option (@)) None xs

  (* PRE: procedure.P.[start&stop] <> G.Call_cfg _. *)
  let inline_call_specs proc_of_name procedure =
    let call_to_spec v = match G.Cfg.V.label v with
      | G.Call_cfg { C.call_name; call_rets; call_args } ->
          let p = proc_of_name call_name in
          let spec = specialize_spec call_rets call_args  p.C.proc_spec in
          G.Cfg.V.create (G.Spec_cfg spec)
      | _ -> v in
    { procedure with P.cfg = G.Cfg.map_vertex call_to_spec procedure.P.cfg }

  let normalize f = f (* {ts=ts; form=form} =
    let form, ts = Clogic.normalise ts form in
    {ts=ts; form=form} *)

  let hashset_subset s1 s2 =
    try HashSet.iter (HashSet.find s2) s1; true with Not_found -> false

  let hashset_equals s1 s2 =
    HashSet.length s1 = HashSet.length s2 &&
    hashset_subset s1 s2

  let extend_precondition vs pre =
    let is_interesting v = CoreOps.is_parameter v || CoreOps.is_global v in
    let eq v = Expr.mk_eq (Expr.mk_var v) (Expr.mk_var (Expr.freshen v)) in
    let vs = List.filter is_interesting vs in
    let xs = pre :: List.map eq vs in
    Expr.mk_big_star xs

  let interpret proc_of_name rules infer procedure = match procedure.C.proc_body with
    | None ->
        if log log_phase then
          fprintf logf "@[Interpreting empty procedure body: %s@\n@]@?" procedure.C.proc_name;
        OK
    | Some body ->
        if log log_phase then
          fprintf logf "@[Interpreting procedure body: %s@\n@]@?" procedure.C.proc_name;
        let body = inline_call_specs proc_of_name body in
        let pvars = collect_pvars body.P.cfg in (* XXX: Use modifies clauses! *)
        let process_triple update triple =
          if log log_phase then
            fprintf logf "@[Processing triple: %a@\n@]@?" CoreOps.pp_triple triple;
          let update = update triple.C.post in
          let pre = extend_precondition pvars triple.C.pre in
          let triple_of_conf { G.current_heap; missing_heap } =
            let ( * ) = Expr.mk_star in
            let pre = pre * missing_heap in
            { C.pre = pre
            ; post = current_heap
            ; modifies = Some pvars } in
          let cs = interpret_flowgraph procedure.C.proc_name update body pre in (* RLP: avoid sending name? *)
          option_map (List.map triple_of_conf) cs in
        let ts = C.TripleSet.elements procedure.C.proc_spec in
        let ts =
          (if infer then begin
            if log log_phase then
              fprintf logf "@[symexec inferring %s@]@\n@?" procedure.C.proc_name;
            let process_triple_infer =
              process_triple (update_infer pvars rules body) in
            let ts = empty_triple :: ts in
            if log log_phase then
              fprintf logf "@[<2>%d candiate triples@]@\n@?" (List.length ts);
            let ts = lol_cat (List.map process_triple_infer ts) in
            let ts = option_map (abstract_triple rules) ts in
            let ts = option [] (fun x->x) ts in (* XXX *)
            ts
          end else ts) in
        if log log_phase then
          fprintf logf "@[symexec checking %s@]@\n@?" procedure.C.proc_name;
        if log log_phase then
          fprintf logf "@[<2>%d candiate triples@]@\n@?" (List.length ts);
        let process_triple_check =
          process_triple (update_check rules.C.calculus body) in
        let ts = lol_cat (List.map process_triple_check ts) in
        let ts = option [] (fun x->x) ts in (* XXX *)
       	(* Check if we are OK or not (see comment for [verify]) *)
        if infer then begin
          let new_ts = failwith "TODO Symexec.interpret new_ts" in
(*             List.filter (fun s -> not (G.P.inconsistent rules s.C.pre)) ts in  *)
	  (* Check if specifications are better. *)
          let old_ts = C.TripleSet.elements procedure.C.proc_spec in
          let not_better nt =
            List.exists (fun ot -> implies_triple rules ot nt) old_ts in
          if List.for_all not_better new_ts then begin
            if log log_exec then begin
              fprintf logf "@[Reached fixed-point for %s@\n@]@?"
                procedure.C.proc_name
            end;
            OK
          end else
            (procedure.C.proc_spec <- C.TripleSet.of_list new_ts;
             if log log_exec then begin
               fprintf logf "@[<2>Abducted triples:";
	       List.iter (fun triple -> fprintf logf "@,{%a}" CoreOps.pp_triple triple) ts;
	       fprintf logf "@]@,@?"
             end;
	     Spec_updated)
	end
	else begin
          let new_specs = C.TripleSet.of_list ts in
	  if C.TripleSet.length new_specs = C.TripleSet.length procedure.C.proc_spec
          then OK
	  else NOK
	end
end
(* }}} *)
(* high level loop for interpreting *) (* {{{ *)
let with_procs q ps = { q with C.q_procs = ps }
let map_procs f q = with_procs q (List.map f q.C.q_procs)

(* Assumes that components come in reversed topological order. *)
let interpret_one_scc proc_of_name q =
  if log log_phase then begin
    fprintf logf "@[Interpreting one scc, with %d procedure(s)@]@,@?"
      (List.length q.C.q_procs)
  end;
  let module PI = ProcedureInterpreter in
  let interpret = PI.interpret proc_of_name q.C.q_rules q.C.q_infer in
  let rec fix () =
    let rs = List.map interpret q.C.q_procs in
    if List.exists ((=) PI.Spec_updated) rs
    then fix ()
    else List.for_all ((=) PI.OK) rs in
  fix ()

let interpret q =
  if log log_phase then
    fprintf logf "@[Interpreting %d procedure(s)@]@,@?" (List.length q.C.q_procs);
  let cg, von = compute_call_graph q.C.q_procs in
  let sccs =
    let module X = Digraph.Components.Make (CallGraph) in
    X.scc_list cg in
  let sccs = List.map (List.map CallGraph.V.label) sccs in
  if !Config.verbosity >= 3 then output_sccs sccs;
  let proc_of_name n = CallGraph.V.label (von n) in
  let qs = List.map (with_procs q) sccs in
  List.for_all (interpret_one_scc proc_of_name) qs

let print_specs ps =
  let triple f t = fprintf f "@\n@[<2>%a@]" CoreOps.pp_triple t in
  let proc f p =
    fprintf f "@\n@[<2>%s%a@]"
      p.C.proc_name
      (pp_list triple) (C.TripleSet.elements p.C.proc_spec) in
  printf "@[<2>@{<g>INFERRED@}:%a@\n@]@?" (pp_list proc) ps

(*
Summary of result of symbolic execution:

Input: {pre} f {post} (we just consider a single function with a single spec for now)
Output:
When run without abduction:
OK if f run on pre implies post
When run with abduction:
{pre’} f {post’} is computed with pre' = pre * Expr for some Expr, then
OK if pre’ is consistent and post’ => post

For a list of specs, we filter out the triples which are OK.
Without abduction, all triples have to be OK for the function to be OK
With abduction, at least one triple has to be OK for the function to be OK.

For a list of functions, all functions have to be OK.
*)
let verify q =
  if log log_exec then
    fprintf logf "@[start verification with abduction=%b@]@,@?" q.C.q_infer;
  let q = map_procs mk_cfg q in
  let r = interpret q in
  if q.C.q_infer && !Config.verbosity >= 1 then print_specs q.C.q_procs;
  if log log_exec then fprintf logf "@]@?";
  r
(* }}} *)
