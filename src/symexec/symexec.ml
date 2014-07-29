(** Symbolic execution (with and without spec inference) happens here. *)
(* modules, constants *) (* {{{ *)
open Corestar_std
open Debug
open Format

module C = Core
module G = Cfg
module P = Cfg.Procedure

let z3_ctx = Syntax.z3_ctx

exception Fatal of string

let bfs_limit = 1 lsl 4
let fix_scc_limit = 1 lsl 2

(* }}} *)
(* helpers, mainly related to expressions *) (* {{{ *)

(** specialize spec to the given actuals

    Warning: If actuals/formals have different lengths, then it makes them equal.
    See [CoreOps.check_well_formed] for an explanation. *)
let specialize_spec a_ps f_ps a_rs f_rs =
  let f { Core.pre; post; modifies } =
    let rec chop (a_s', f_s') = function
      | _, [] -> (List.rev a_s', List.rev f_s')
      | [], f :: f_s -> chop (Syntax.freshen f :: a_s', f :: f_s') ([], f_s)
      | a :: a_s, f :: f_s -> chop (a :: a_s', f :: f_s') (a_s, f_s) in
    let a_ps', f_ps' = chop ([], []) (a_ps, f_ps) in
    let a_rs', f_rs' = chop ([], []) (a_rs, f_rs) in
    { Core.pre = Z3.Expr.substitute pre f_ps' a_ps'
    ; post = Z3.Expr.substitute post (f_ps' @ f_rs') (a_ps' @ a_rs')
    ; modifies = a_rs @ modifies (* old rets, so it havocs extra returns *) } in
  C.TripleSet.map f

let mk_big_star = Prover.mk_big_star
let mk_star = Prover.mk_star

let freshen_triple { C.pre; post; modifies } =
  let h = Syntax.ExprHashMap.create 0 in
  let rec freshen_expr e =
    let var v = if not (Syntax.is_lvar v) then v else begin
      try Syntax.ExprHashMap.find h v
      with Not_found ->
        (let w = Syntax.freshen v in Syntax.ExprHashMap.add h v w; w)
    end in
    (Syntax.on_var var & Syntax.recurse freshen_expr) e in
  { C.pre = freshen_expr pre; post = freshen_expr post; modifies }

let simplify_triple ({ C.pre; post; modifies } as t1) =
  let module H = Hashtbl.Make (Syntax.HashableExpr) in

  let dbg_eq f (a, b) =
    fprintf f "@[%a=%a@]" Syntax.pp_expr a Syntax.pp_expr b in
  let dbg_eqs f eqs =
    fprintf f "@[<2>(eqs@ @[%a@])@]" (pp_list_sep " * " dbg_eq) eqs in
(*  let dbg_reps f rs =
    dbg_eqs f (H.fold (fun e f eqs -> (e, f) :: eqs) rs []) in
*)
  let rec get_eqs is_ok e =
    let eq a b = if is_ok a || is_ok b then [(a, b)] else [] in
    let star a b = get_eqs is_ok a @ get_eqs is_ok b in
    (Syntax.on_eq eq & Syntax.on_star star & c1 []) e in
  let rec get_lvars e =
    let var v = if Syntax.is_lvar v then [v] else [] in
    (Syntax.on_var var & Syntax.on_app (fun _ es -> es >>= get_lvars)) e in
  let is_ve p e = Syntax.on_var p (c1 false) e in
  let is_lvar = is_ve Syntax.is_lvar in
  let is_pvar = is_ve Syntax.is_pvar in
  let is_var e = is_lvar e || is_pvar e in
  let get_reps e =
    let h = H.create 0 in
    let eqs = get_eqs is_var e in
    let rec find e =
      let f = (try H.find h e with Not_found -> e) in
      let f = if Syntax.expr_equal e f then e else find f in
      H.replace h e f; f in
    let union (a, b) =
      let a, b = find a, find b in
      let a, b =
        if is_lvar b || not (is_var b || is_lvar a) then b, a else a, b in
      H.replace h a b in
    List.iter union eqs;
    let es = H.fold (fun k _ ks -> k :: ks) h [] in
    List.iter (ignore @@ find) es;
    h in
  let pre_reps, post_reps = get_reps pre, get_reps post in
  let common xs ys =
    let h = H.create 0 in
    let add_rep x =
      (try H.replace h (H.find pre_reps x) () with Not_found -> ()) in
    List.iter add_rep xs;
    let f zs y =
      try
        let yy = H.find pre_reps y in
        if H.mem h yy then (H.remove h yy; y :: zs) else zs
      with Not_found -> zs in
    List.fold_left f [] ys in
  let ls = common (get_lvars pre) (get_lvars post) in
  let mk_subst rep =
    H.fold (fun e f (subees,subers) ->
      if is_lvar e then (e::subees, f::subers) else (subees, subers)) rep ([],[]) in
  let (pre_subees, pre_subers) = mk_subst pre_reps in
  let (post_subees, post_subers) = mk_subst post_reps in
  let pre = Z3.Expr.substitute pre pre_subees pre_subers in
  let post = Z3.Expr.substitute post post_subees post_subers in
  let lvar_eqs rep =
    let f v = (try [Z3.Boolean.mk_eq z3_ctx v (H.find rep v)] with Not_found -> []) in
    ls >>= f in
  let pre = mk_big_star (pre :: lvar_eqs pre_reps) in
  let post = mk_big_star (post :: lvar_eqs post_reps) in
  let pre = Prover.normalize pre in
  let post = Prover.normalize post in
  let t2 = { C.pre; post; modifies } in
  printf "@[<2>(simplify_triple@ @[(%a)→(%a)@]@\npre_subst@ %a\
      @\npost_subst@ %a@\ncommon_pre@ %a@\ncommon_post@ %a@])@\n"
    CoreOps.pp_triple t1
    CoreOps.pp_triple t2
    dbg_eqs (List.combine pre_subees pre_subers)
    dbg_eqs (List.combine post_subees post_subers)
    (pp_list_sep " * " Syntax.pp_expr) (lvar_eqs pre_reps)
    (pp_list_sep " * " Syntax.pp_expr) (lvar_eqs post_reps)
    ;
  t2

let normalize { C.pre; post; modifies } =
  let f = Prover.normalize in
  { C.pre = f pre; post = f post; modifies }

let normalize_spec = C.TripleSet.map normalize

let normalize_proc proc =
  proc.C.proc_spec <- normalize_spec proc.C.proc_spec

let join_triples ts =
  printf "@[<2>(ENTER join_triples (%a)@]@\n"
    (pp_list_sep "+" CoreOps.pp_triple) ts;
  let pre = Prover.mk_big_meet (List.map (fun t -> t.C.pre) ts) in
  let post = Prover.mk_big_or (List.map (fun t -> t.C.post) ts) in
  let modifies =
    Misc.remove_duplicates Syntax.expr_compare (ts >>= fun t -> t.C.modifies) in
  printf "LEAVE join_triples)@\n";
  { C.pre; post; modifies }


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

let mk_intermediate_cfg params ret_vars cs =
  let g = CfgH.create () in
  let start, stop, succ = mic_create_vertices g cs in
  let labels = mic_hash_labels g in
  let r =
    { ProcedureH.cfg = g
    ; ProcedureH.start = start
    ; ProcedureH.stop = stop
    ; ProcedureH.parameters = params
    ; ProcedureH.return_vars = ret_vars } in
  mic_add_edges r labels succ;
  r

(* helpers for [simplify_cfg] {{{ *)
let sc_interesting_label = function
  | C.Call_core _ | C.Assignment_core _ -> true
  | _ -> false

let sc_new_label = function
  | C.Assignment_core a ->
      G.Spec_cfg
        ( specialize_spec
            a.C.asgn_args a.C.asgn_args_formal
            a.C.asgn_rets a.C.asgn_rets_formal
            a.C.asgn_spec )
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

let simplify_cfg { ProcedureH.cfg; start; stop; parameters; return_vars } =
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
  ; stop = HVHashtbl.find nv stop
  ; parameters
  ; return_vars }

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
  let g = option_map (mk_intermediate_cfg  q.C.proc_args q.C.proc_rets) q.C.proc_body in
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
(* Fixed point calculation will stop when this number of triples is reached *)
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
  module StatementBfs = Bfs.Make (SS)
  module ConfBfs = Bfs.Make (CS)

  (* helpers for configuration graphs *) (* {{{ *)

  (* The following algorithm is used to compute which confs inevitably lead to
  error, and also to compute whether a set of confs associated with the stop
  vertex covers all possible demonic choices. In general, for each vertex x we
  are given an integer c(x). The returned value is the least fixed-point of: If
  at least c(x) successors of x are marked, then x is marked.  (Note that c(x)=0
  implies that x is in the result.) Works in linear time/space. *)
  let eval_cg init confgraph =
    let count = CD.create 0 in
    let q = ConfBfs.initialize true in
    let init x =
      let c = init x in
      if c = 0 then ConfBfs.enque q x;
      assert (not (CD.mem count x));
      CD.add count x c in
    let decrement x =
      if not (ConfBfs.is_seen q x) then begin
        let c = CD.find count x - 1 in
        assert (c >= 0);
        if c = 0 then ConfBfs.enque q x;
        CD.replace count x c
      end in
    let process x =
      assert (CD.find count x = 0);
      CG.iter_pred decrement confgraph x in
    CG.iter_vertex init confgraph;
    while not (ConfBfs.is_done q) do process (ConfBfs.deque q) done;
    CS.of_list (ConfBfs.get_seen q)


  (* }}} *)

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
  Then it calls [abstract] on the whole set of post-confs. The [confgraph] is
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

  let initialize procedure (pre_formula, pre_defs) =
    let confgraph = CG.create () in
    let flowgraph = procedure.P.cfg in
    let post_of = SD.create 1 in
    let pre_of = SD.create 1 in
    let statement_of = CD.create 1 in
    let conf =
      let ok_conf =
        { G.current_heap = pre_formula
        ; missing_heap = Syntax.mk_emp
        ; pvar_value = pre_defs } in
      (*   TODO:   G.check_ok_configuration ok_conf; *)
      CG.V.create (G.OkConf (ok_conf, G.Demonic)) in
    CG.add_vertex confgraph conf;
    CD.add statement_of conf procedure.P.start;
    SD.add post_of procedure.P.start (CS.singleton conf);
    { confgraph; flowgraph; post_of; pre_of; statement_of }


  let abduct = Prover.biabduct
  let frame = Prover.infer_frame

  let collect_pvars fg =
    let cp_vertex v acc = match G.Cfg.V.label v with
      | G.Abs_cfg | G.Nop_cfg -> acc
      | G.Call_cfg { C.call_rets; call_name; call_args } ->
          failwith "INTERNAL: calls should be removed by [inline_call_specs]"
      | G.Spec_cfg spec ->
          let cp_triple { Core.pre; post } acc =
            let cp_formula f =
              let vs = Syntax.ExprSet.filter Syntax.is_pvar (Syntax.vars f) in
              Syntax.ExprSet.union vs in
            acc |> cp_formula pre |> cp_formula post in
          C.TripleSet.fold cp_triple spec acc
    in
    Syntax.ExprSet.elements (G.Cfg.fold_vertex cp_vertex fg Syntax.ExprSet.empty)

  let collect_modified_vars fg =
    let cp_vertex v acc = match G.Cfg.V.label v with
      | G.Abs_cfg | G.Nop_cfg -> acc
      | G.Call_cfg _ ->
          failwith "INTERNAL: calls should be removed by [inline_call_specs]"
      | G.Spec_cfg spec ->
          let cm_triple t = List.fold_right Syntax.ExprSet.add t.C.modifies in
          C.TripleSet.fold cm_triple spec acc in
    Syntax.ExprSet.elements (G.Cfg.fold_vertex cp_vertex fg Syntax.ExprSet.empty)

  (* TODO: More efficient? *)
  let substitute_defs ds e =
    let (subees, subers) = List.split (Syntax.ExprMap.bindings ds) in
    Z3.Expr.substitute e subees subers

  (* If we execute a statement that has [post] as a postcondition, and modifies
  the variables in [vs], then the pre-state [pre_defs] is modified as follows:
  if a program variable [x] is not in [vs], then it remains unchanged; if it
  is in [vs] then, as a last resort we give it a fresh logical variable (aka
  value) in the post-state; but, first, we analyze the postcondition to see if
  it contains an equality [x=E] such that [post_defs(E)] can be computed.
  NOTE: cycles, such as an equality [x=x] make us to fall back to the fresh
  variable solution. *)
  exception Done
  let update_defs pre_defs vs post =
    let is_v =
      flip Syntax.ExprSet.mem (List.fold_right Syntax.ExprSet.add vs Syntax.ExprSet.empty) in
    let vs_of = Syntax.ExprSet.filter is_v @@ Syntax.vars in
    let rec get_pdefs pdefs e =
      let eq a b =
        let va, vb = is_v a, is_v b in
        if va || vb then begin
          let v, e = if va then a, b else b, a in
          let ds = (try Syntax.ExprMap.find v pdefs with Not_found -> []) in
          Syntax.ExprMap.add v ((e, vs_of e) :: ds) pdefs
        end else pdefs in
      let star a b = get_pdefs (get_pdefs pdefs a) b in
      ( Syntax.on_eq eq
      & Syntax.on_star star
      & c1 pdefs )
      e in
    let pdefs = get_pdefs Syntax.ExprMap.empty post in
    let post_defs = ref (List.fold_right Syntax.ExprMap.remove vs pre_defs) in
    let seen = Syntax.ExprHashSet.create 0 in
    let rec define v = if not (Syntax.ExprHashSet.mem seen v) then begin
      Syntax.ExprHashSet.add seen v;
      let process_eq (e, ws) =
        Syntax.ExprSet.iter define ws;
        if Syntax.ExprSet.for_all (flip Syntax.ExprMap.mem !post_defs) ws then begin
          let e = substitute_defs !post_defs e in
          post_defs := Syntax.ExprMap.add v e !post_defs;
          raise Done
        end
      in
      let eqs = (try Syntax.ExprMap.find v pdefs with Not_found -> []) in
      (try List.iter process_eq eqs with Done -> ())
    end in
    List.iter define vs;
    (* TODO: Below, no attempt is made to minimize the number of fresh vars. *)
    let mk_fresh v = if not (Syntax.ExprMap.mem v !post_defs) then
      post_defs := Syntax.ExprMap.add v (Syntax.freshen v) !post_defs in
    List.iter mk_fresh vs;
    !post_defs

  let eqs_of_bindings ds =
    let mk_eq (v, e) = Z3.Boolean.mk_eq z3_ctx v e in
    ds |> List.map mk_eq |> Syntax.mk_big_star

  (* helpers for [execute_one_triple] *) (* {{{ *)

  (* TODO: Really, make that function nicer. *)

  (* }}} *)

  (* The prover answers a query H⊢P with a list F1⊢A1, ..., Fn⊢An of assumptions
  that are sufficient.  This implies that H*(A1∧...∧An)⊢P*(F1∨...∨Fn).  It is
  sufficient to demonically split on the frames Fk, and then angelically on the
  antiframes Ak.  Further, it is sufficient to demonically split on (antiframe,
  frame) pairs (Ak, Fk). *)
  let execute_one_triple abstract_afs abduct is_deadend pre_conf triple =
    if log log_exec then
      fprintf logf "@[<2>@{<p>execute %a@ from %a@ to get@\n"
        CoreOps.pp_triple triple
        Cfg.pp_ok_configuration pre_conf;
    let { C.pre; post; modifies } = triple in
    let vs = modifies in
    let pre_defs = pre_conf.G.pvar_value in
    let def_eqs = eqs_of_bindings (Syntax.ExprMap.bindings pre_defs) in
    let afs = abduct (mk_star pre_conf.G.current_heap def_eqs) pre in
    let branch afs =
      let afs = abstract_afs afs in
      (* TODO: distribute the pure part of antiframes to all demonic choices *)
      let mk_post_conf { Prover.antiframe = a; frame = f } =
        let post_defs = update_defs pre_defs vs post in
        let f = substitute_defs pre_defs f in
        let post = substitute_defs post_defs post in
        let a = substitute_defs pre_defs a in
        let h = Prover.normalize (mk_star post f) in
        let hs = (Syntax.on_or id & Syntax.on_app (c2 [h])) h in
        let missing_heap = mk_star pre_conf.G.missing_heap a in
        let mk current_heap =
          { G.current_heap; missing_heap; pvar_value = post_defs } in
(*  TODO       G.check_ok_configuration conf; *)
        let cs = List.map mk hs in
        if log log_exec then begin
          fprintf logf "@[<2>(demonic choice: %a)@]@\n"
            (pp_list_sep " or " Cfg.pp_ok_configuration) cs
        end;
        cs in
      let mk_ok conf = CT_ok conf in
      let keep_conf { G.missing_heap; current_heap; pvar_value } =
        let current_heap =
          mk_star
            current_heap (eqs_of_bindings (Syntax.ExprMap.bindings pvar_value)) in
        not (is_deadend missing_heap) && not (is_deadend current_heap) in
      afs
        >>= mk_post_conf
        |> List.filter keep_conf
        |> List.map mk_ok
        |> make_demonic_choice in
    let r = match afs with
      (* TODO: The [] is insufficient! *)
      | [] -> (* abduct failed, see prover.mli *)
          if log log_exec then
            fprintf logf "(error conf)@?";
          CT_error
      | afs -> branch afs in
    if log log_exec then fprintf logf "@}@]@,@?";
    r

  let execute abstract_afs abduct is_deadend =
    let execute_one_triple =
      execute_one_triple abstract_afs abduct is_deadend in
    fun spec_of pre_conf statement ->
      statement
      |> spec_of
      |> C.TripleSet.elements
      |> List.map (execute_one_triple pre_conf)
      |> make_angelic_choice

  (* [abstract], below, needs impredicative polymorphism. *)
  type ('x, 'xs) abs_collection =
    { ac_name : string
    ; ac_fold : 'acc. ('x -> 'acc -> 'acc) -> 'xs -> 'acc -> 'acc
    ; ac_add : 'x -> 'xs -> 'xs
    ; ac_mk : unit -> 'xs }

  let abstract ac add_edge implies confs =
    let tcnt, fcnt = ref 0, ref 0 in
    let implies a b =
      let r = implies a b in
      if r then incr tcnt else incr fcnt;
      r in

    let add_edges l c = List.iter (flip add_edge c) l in
    let partition add_ns (ys, ns) p xs =
      let f x (ys, ns) =
        if p x then (x :: ys, ns) else (ys, add_ns x ns) in
      ac.ac_fold f xs (ys, ns) in
    let find p xs = fst (partition (c2 ()) ([], ()) p xs) in

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
    let r = ac.ac_fold f confs (ac.ac_mk ()) in
    if log log_exec then
      fprintf logf "%s tcnt %d fcnt %d@\n" ac.ac_name !tcnt !fcnt;
    r

  let implies_conf calculus v1 v2 = match CG.V.label v1, CG.V.label v2 with
    | G.ErrorConf, G.ErrorConf -> true
    | G.ErrorConf, _ | _, G.ErrorConf -> false
    | G.OkConf ( { G.current_heap = c1; missing_heap = m1; pvar_value = b1 }, _)
    , G.OkConf ( { G.current_heap = c2; missing_heap = m2; pvar_value = b2 }, _)
      ->
        let eqs b = eqs_of_bindings (Syntax.ExprMap.bindings b) in
        let c1 = mk_star c1 (eqs b1) in
        let c2 = mk_star c2 (eqs b2) in
        Prover.is_entailment calculus c1 c2
        && Prover.is_entailment calculus m2 m1

  let implies_triple calculus t1 t2 =
    let t2m = List.fold_right Syntax.ExprSet.add t2.C.modifies Syntax.ExprSet.empty in
    let prove = Prover.infer_frame calculus in
    let check_final { Prover.frame; _ } = Syntax.is_pure frame in
    let check_intermediate { Prover.frame; _ } =
      List.exists check_final (prove (mk_star frame t1.C.post) t2.C.post) in
    let r =
      List.for_all (flip Syntax.ExprSet.mem t2m) t1.C.modifies
      && List.exists check_intermediate (prove t2.C.pre t1.C.pre) in
    if log log_exec then begin
      fprintf logf "@[<2>implies_triple: %b@ @[%a@ =?=> %a@]@]@\n"
        r CoreOps.pp_triple t1 CoreOps.pp_triple t2;
    end;
    r

  (* The notation "weakest" and "implies" refer only to the current heap.
     For ok_configurations (M1, H1) and (M2, H2), we observe that

     [[(M1, H1)]] /\ M2 => M1 /\ H1 => H2
     ------------------------------------
             [[(M2, H2)]]

     where [[(M, H)]] is roughly that "if M is added to the preconditon, then H will be true of the current heap".

     In this sense, implies (M1, H1) (M2, H2) actually checks
     [[(M2, H2)]] => [[(M1, H1)]]. *)
  let abstract_conf =
    let n = ref 0 in
    fun calculus confgraph cs ->
      (* Profiling says that without this trick we spend a lot of time
      figuring out that there's nothing to abstract. *)
      incr n;
      if !n mod 100 <> 0
      then cs
      else
        abstract
          { ac_name = "confset"
          ; ac_fold = CS.fold
          ; ac_add = (fun x xs -> CS.add xs x; xs)
          ; ac_mk = (fun () -> CS.create 0) }
          (CG.add_edge confgraph) (implies_conf calculus) cs
  let abstract_triple calculus =
    printf "abstract_triple@\n";
    abstract
      { ac_name = "triplelist"
      ; ac_fold = List.fold_right
      ; ac_add = (fun x xs -> x :: xs)
      ; ac_mk = (fun () -> []) }
      (fun _ _ -> ())
      (flip (implies_triple calculus))

  let abstract_afs calculus =
    abstract
      { ac_name = "antiframe_frame_pair_list"
      ; ac_fold = List.fold_right
      ; ac_add = ListH.cons
      ; ac_mk = (fun () -> []) }
      (c2 ())
      (fun af1 af2 ->
        Prover.is_entailment calculus af1.Prover.frame af2.Prover.frame)

  (* helpers for [prune_error_confs] {{{ *)

  let pec_get_errors confgraph =
    let count x = match CG.V.label x with
      | G.OkConf (_, G.Angelic) -> CG.fold_succ (c1 succ) confgraph x 0
      | G.OkConf (_, G.Demonic) -> 1
      | G.ErrorConf -> 0 in
    eval_cg count confgraph

  (* Finds confs reachable from [inits] without going thru [errors]. *)
  let pec_get_to_keep confgraph inits errors =
    let q = ConfBfs.initialize true in
    let enque c = if not (CS.mem errors c) then ConfBfs.enque q c in
    CS.iter enque inits;
    while not (ConfBfs.is_done q) do
      CG.iter_succ enque confgraph (ConfBfs.deque q)
    done;
    CS.of_list (ConfBfs.get_seen q)

  let pec_get_to_remove confgraph to_keep =
    let to_remove = CS.create 0 in
    let rm v = if not (CS.mem to_keep v) then CS.add to_remove v in
    CG.iter_vertex rm confgraph;
    to_remove

  (* }}} *)

  (* Keeps those configurations that are reachable from [post_confs context
  start], and can avoid error thru angelic choices. *)
  let prune_error_confs context start =
    let confgraph = context.confgraph in
    let inits = post_confs context start in
    let errors = pec_get_errors confgraph in
    let to_keep = pec_get_to_keep confgraph inits errors in
    let to_remove = pec_get_to_remove confgraph to_keep in
    CS.iter (remove_conf context) to_remove

  let confgraph_counter = ref 0
  let output_confgraph_i stops n i g =
    if !confgraph_counter < 1000 then begin
      let ccc = incr confgraph_counter; !confgraph_counter in
      let fname = sprintf "%s_confgraph_%05d_%d.dot" n ccc i in
      if log log_exec then fprintf logf "@[Outputing confgraph to file: @{<dotpdf>%s@}@]@\n@?" fname;
      G.fileout_confgraph stops fname g
    end

  (* helpers for [get_stop_confs] *) (* {{{ *)

  let gsc_is_ok confgraph starts stops confs =
    let no_succ x = CG.fold_succ (c2 false) confgraph x true in
    let count x =
      if CS.mem confs x then 0
      else if CS.mem stops x then (assert (no_succ x); 1)
      else (match CG.V.label x with
        | G.OkConf (_, G.Angelic) -> 1
        | G.OkConf (_, G.Demonic) -> CG.fold_succ (c1 succ) confgraph x 0
        | G.ErrorConf -> failwith "INTERNAL: errors should be pruned by now") in
    let covered = eval_cg count confgraph in
    CS.for_all (CS.mem covered) starts

  (* NOTE: The problem solved here is at least as hard as generating hitting
  sets, for which no output-polynomial time is known. That's why it's OK to use
  a rather stupid approximation. For some definition of OK. *)
  let gsc_group confgraph starts cs =
    let is_ok = gsc_is_ok confgraph starts cs in
    let cs = CS.elements cs in
    assert (List.length cs < 100); (* Otherwise this may take forever. *)
    let shrink cs =
      let ds = CS.of_list cs in
      let f c = CS.remove ds c; if not (is_ok ds) then CS.add ds c in
      List.iter f cs;
      CS.elements ds in
    let remaining = CS.of_list cs in
    let rec loop css =
      if is_ok remaining then
        let cs = shrink (CS.elements remaining) in
        if cs = [] then [[]] else begin
          List.iter (CS.remove remaining) cs;
          loop (cs :: css)
        end
      else css in
    let css = if CS.length starts = 0 then [] else loop [] in
    if log log_exec then begin
      let n = ref 0 in
      let ppg f cs =
        incr n;
        fprintf f "@[<2>group %d:@ %a@]@\n"
          !n
          (pp_list_sep "+" G.pp_configuration) cs in
      let css = List.map (List.map CG.V.label) css in
      fprintf logf "@[<2>stop confs (%d):@ %a@]@\n@?"
        (List.length css) (pp_list ppg) css
    end;
    css

  (* }}} *)

  (* TODO: Group configurations such that they cover all demonic choices. *)
  let get_stop_confs context proc =
    prune_error_confs context proc.P.start;
    post_confs context proc.P.stop
      |> gsc_group context.confgraph (post_confs context proc.P.start)
      |> List.map (List.map conf_of_vertex)

  (* Builds a graph of configurations, in BFS order. *)
  let interpret_flowgraph proc_name update procedure pre =
    let context = initialize procedure pre in
    let q = StatementBfs.initialize false in
    let enque_succ = G.Cfg.iter_succ (StatementBfs.enque q) context.flowgraph in
    enque_succ procedure.P.start;
    let rec bfs budget =
      if log log_exec then begin
        let stops = post_confs context procedure.P.stop in
        output_confgraph_i stops proc_name budget context.confgraph
      end;
      if budget = 0 || StatementBfs.is_done q then budget else begin
        let s = StatementBfs.deque q in
        if update context s then enque_succ s;
        bfs (budget - 1)
      end in
    if bfs bfs_limit = 0 then begin
      if log log_exec then
        fprintf logf "@[interpret_flowgraph limit reached@]@\n";
      None
    end
    else begin
      Some (get_stop_confs context procedure)
    end

  let empty_triple =
    { Core.pre = Syntax.mk_emp; post = Syntax.mk_emp; modifies = [] }

  let spec_of post =
    let post = CoreOps.mk_assert post in
    let nop = C.TripleSet.singleton empty_triple in
    fun stop statement ->
    if statement = stop
    then begin assert (G.Cfg.V.label statement = G.Nop_cfg); post end
    else begin match G.Cfg.V.label statement with
      | G.Abs_cfg | G.Nop_cfg -> nop
      | G.Spec_cfg s -> C.TripleSet.map freshen_triple s
      | G.Call_cfg { C.call_rets; call_name; call_args } ->
          assert false (* should have called [inline_call_specs] before *)
    end

  let update_gen ask rules body post =
    let ask = ask rules.C.calculus in
    let is_deadend = Prover.is_inconsistent rules.C.calculus in
    let abstract_afs = abstract_afs rules.C.calculus in
    let execute = execute
      abstract_afs ask is_deadend (spec_of post body.P.stop) in
    update execute (abstract_conf rules.C.calculus)

  let update_infer = update_gen abduct
  let update_check = update_gen frame

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
          let spec =
            specialize_spec
              call_args p.C.proc_args
              call_rets p.C.proc_rets
              p.C.proc_spec in
          G.Cfg.V.create (G.Spec_cfg spec)
      | _ -> v in
    { procedure with P.cfg = G.Cfg.map_vertex call_to_spec procedure.P.cfg }

  (* TODO: This function is huge: must be refactored into smaller pieces. *)
  let interpret proc_of_name rules infer procedure = match procedure.C.proc_body with
    | None ->
        if log log_phase then
          fprintf logf "@[@{<p>Interpreting empty procedure body: %s@}@\n@]@?" procedure.C.proc_name;
        OK
    | Some body ->
        if log log_phase then
          fprintf logf "@{<details>@[@{<summary>Interpreting procedure body: %s@}@\n@]@?" procedure.C.proc_name;
        let body = inline_call_specs proc_of_name body in
        let mvars = collect_modified_vars body.P.cfg in
        let mvars_global = List.filter Syntax.is_pgvar mvars in
        let pvars = collect_pvars body.P.cfg in
        let process_triple update triple =
          if log log_phase then
            fprintf logf "@{<details>@[@{<summary>Processing triple: %a@}@\n@]@?" CoreOps.pp_triple triple;
          let pre_defs = update_defs Syntax.ExprMap.empty pvars triple.C.pre in
          let is_init_value =
            let init = Syntax.ExprHashMap.create 0 in
            Syntax.ExprMap.iter (fun _ v -> Syntax.ExprHashMap.replace init v ()) pre_defs;
            Syntax.ExprHashMap.mem init in
          let update = update triple.C.post in
          let triple_of_conf { G.current_heap; missing_heap; pvar_value } =
            let visible_defs =
              let p v _ = Syntax.is_pgvar v || (List.exists (Syntax.expr_equal v) procedure.C.proc_rets) in
              Syntax.ExprMap.filter p pvar_value in
            let pre_eqs = eqs_of_bindings (Syntax.ExprMap.bindings pre_defs) in
            let post_eqs =
              (* TODO(rgrig): Fix. This is horrible code. *)
              let module H = Hashtbl.Make (Syntax.HashableExpr) in
              let h = H.create 0 in
              let add e x =
                let xs = (try H.find h e with Not_found -> []) in
                H.replace h e (x :: xs) in
              Syntax.ExprMap.iter (flip add) visible_defs;
              let rec is_init e =
                is_init_value e ||
                  (Syntax.on_app (c1 & List.for_all is_init)) e in
              let get_classes e xs ess =
                let es = if is_init e then e :: xs else xs in
                es :: ess in
              let ess = H.fold get_classes h [] in
              let add_eq eqs e1 e2 = Z3.Boolean.mk_eq z3_ctx e1 e2 :: eqs in
              let eqs = List.fold_left (Misc.fold_pairs add_eq) [] ess in
              mk_big_star eqs in
	    (* substitute expressions for their associated visible variable *)
	    let (subers, subees) = List.split (Syntax.ExprMap.bindings visible_defs) in
            let current_heap = Z3.Expr.substitute current_heap subees subers in
            (* TODO: what if lvars remain after the above substitutions? *)
            simplify_triple
              { C.pre = mk_big_star [triple.C.pre; missing_heap; pre_eqs]
              ; post = mk_star current_heap post_eqs
              ; modifies = mvars_global } in
          let css =
            let name = procedure.C.proc_name in
            let pre = (substitute_defs pre_defs triple.C.pre, pre_defs) in
            interpret_flowgraph name update body pre in (* RLP: avoid sending name? *)
          let tss = option_map (List.map (List.map triple_of_conf)) css in
          let ts = option_map (List.map join_triples) tss in
          if log log_phase then fprintf logf "@}@?";
	  ts in
        let ts = C.TripleSet.elements procedure.C.proc_spec in
        let ts =
          (if infer then begin
            if log log_phase then
              fprintf logf "@[@{<h4>symexec inferring %s@}@]@\n@?" procedure.C.proc_name;
            let process_triple_infer =
              process_triple (update_infer rules body) in
            let ts = empty_triple :: ts in
            if log log_phase then
              fprintf logf "@[<2>@{<p>%d candidate triples@}@]@\n@?" (List.length ts);
            let ts = lol_cat (List.map process_triple_infer ts) in
            let ts = option_map (abstract_triple rules.C.calculus) ts in
            let ts = option [] id ts in
            ts
          end else ts) in
        if log log_phase then
          fprintf logf "@[@{<h4>symexec checking %s@}@]@\n@?" procedure.C.proc_name;
        if log log_phase then
          fprintf logf "@[<2>@{<p>%d candidate triples@}@]@\n@?" (List.length ts);
        let process_triple_check =
          process_triple (update_check rules body) in
        let tss = List.map process_triple_check ts in
        if log log_phase then fprintf logf "@}";
       	(* Check if we are OK or not (see comment for [verify]) *)
        if infer then begin
          let ts = lol_cat tss in
          let ts = option [] id ts in
          let new_ts =
            (* TODO: each disjunct of the pre should be filtered using
            is_inconsistent; but check it doesn't get too slow *)
            let f t = not (Prover.is_inconsistent rules.C.calculus t.C.pre) in
            List.filter f ts in
	  (* Check if specifications are better. *)
          let old_ts = C.TripleSet.elements procedure.C.proc_spec in
          let not_better nt =
            let implied_by = flip (implies_triple rules.C.calculus) in
            List.exists (implied_by nt) old_ts in
          if List.for_all not_better new_ts then begin
            if log log_exec then begin
              fprintf logf "@[@{<h3>Reached fixed-point for %s@}@\n@]@?"
                procedure.C.proc_name
            end;
            if log log_phase then fprintf logf "@{</details>@?";
            OK
          end else (
            let remove_locals t =
	      (* only global variables matter in the modifies *)
	      let mods = List.filter Syntax.is_pgvar t.C.modifies in
	      { t with C.modifies = mods } in
	    let new_ts = List.map remove_locals new_ts in
	    procedure.C.proc_spec <- C.TripleSet.of_list new_ts;
            if log log_exec then begin
              fprintf logf "@[<2>@{<h4>Abducted triples:@}";
	      List.iter (fun triple -> fprintf logf "@,{%a}" CoreOps.pp_triple triple) ts;
	      fprintf logf "@]@,@?"
            end;
            if log log_phase then fprintf logf "@{</details>@?";
	    Spec_updated)
	end
	else begin (* checking, not inferring *)
          let modifies_ok t =
            let ms =
              List.fold_right Syntax.ExprSet.add t.C.modifies Syntax.ExprSet.empty in
            List.for_all (flip Syntax.ExprSet.mem ms) mvars_global in
          let ok =
            List.for_all (option false ((<>) [])) tss
            && C.TripleSet.for_all modifies_ok procedure.C.proc_spec in
          if ok then OK else NOK
	end
end
(* }}} *)
(* high level loop for interpreting *) (* {{{ *)
let with_procs q ps = { q with C.q_procs = ps }
let map_procs f q = with_procs q (List.map f q.C.q_procs)

(* Assumes that components come in reversed topological order. *)
let interpret_one_scc proc_of_name q =
  if log log_phase then begin
    fprintf logf "@[@{<p>Interpreting one scc, with %d procedure(s)@}@]@,@?"
      (List.length q.C.q_procs)
  end;
  let module PI = ProcedureInterpreter in
  let interpret = PI.interpret proc_of_name q.C.q_rules q.C.q_infer in
  let rec fix limit =
    if log log_exec && limit = 0 then
      fprintf logf "fix_scc_limit reached@\n";
    let rs = List.map interpret q.C.q_procs in
    if limit <> 0 && List.exists ((=) PI.Spec_updated) rs
    then fix (limit-1)
    else List.for_all2 (fun r p -> (r = PI.OK) = p.C.proc_ok) rs q.C.q_procs in
  fix fix_scc_limit

let interpret q =
  if log log_phase then
    fprintf logf "@[@{<p>Interpreting %d procedure(s)@}@]@,@?" (List.length q.C.q_procs);
  let cg, von = compute_call_graph q.C.q_procs in
  let sccs =
    let module X = Digraph.Components.Make (CallGraph) in
    X.scc_list cg in
  let sccs = List.map (List.map CallGraph.V.label) sccs in
  if !Config.verbosity >= 3 then output_sccs sccs;
  let proc_of_name n = CallGraph.V.label (von n) in
  let qs = List.map (with_procs q) sccs in
  (* NOTE: We do *not* want to stop early if an SCC fails. *)
  let rs = List.map (interpret_one_scc proc_of_name) qs in
  List.for_all id rs

let print_specs ps =
  let triple f t = fprintf f "@\n@[<2>%a@]" CoreOps.pp_triple t in
  let proc f p =
    fprintf f "@\n@{<p>@[<2>%s%a@]@}"
      p.C.proc_name
      (pp_list triple) (C.TripleSet.elements p.C.proc_spec) in
  printf "@[<2>@{<h3>@{<g>INFERRED@}:@}%a@\n@]@?" (pp_list proc) ps

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
  prof_phase "well-formedness checks";
  CoreOps.is_well_formed q && begin
    prof_phase "preprocess for symexec";
    List.iter normalize_proc q.C.q_procs;
    if log log_exec then
      fprintf logf "@[<2>@{<details>@{<summary>got question@}@\n%a@}@?" CoreOps.pp_ast_question q;
    let q = map_procs mk_cfg q in
    prof_phase "symexec";
    let r = interpret q in
    if q.C.q_infer && !Config.verbosity >= 1 then print_specs q.C.q_procs;
    if log log_exec then fprintf logf "@]@\n@?";
    r
  end
(* }}} *)
