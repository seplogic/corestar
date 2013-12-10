(********************************************************
   This file is part of coreStar
	src/prover/smt.ml
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   coreStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)


open Clogic
open Congruence
open Corestar_std
open Cterm
open Debug
open Format
open List
open Psyntax
open Smtsyntax
open Unix
open Config

exception SMT_error of string
exception SMT_fatal_error

(*let Config.smt_run = ref true;; *)
let smt_fdepth = ref 0;;
let smtout = ref Pervasives.stdin;;
let smtin = ref Pervasives.stderr;;
let smterr = ref Pervasives.stdin;;
let smtpath = ref ""

let smtout_lex = ref (Lexing.from_string "");;

let smt_memo = Hashtbl.create 31;;

let smt_onstack = ref [[]];;

let send_custom_commands =
  let decl_re = Str.regexp "[ \t]*([ \t]*declare-fun[ \t]+\\([^ \t()]+\\)" in
  fun () ->
    if !Config.smt_custom_commands <> "" then (
      let cc = open_in !Config.smt_custom_commands in
      try while true do begin
	let cmd = input_line cc in
	if log log_smt then fprintf logf "@[%s@." cmd;
	if Str.string_match decl_re cmd 0 then
	  predeclared := RegexpSet.add (Str.regexp_string (Str.matched_group 1 cmd)) !predeclared;
	output_string !smtin cmd;
	output_char !smtin '\n'
      end done
      with End_of_file -> close_in cc
    )

let smt_declare_datatype dtid decl =
  if log log_smt then fprintf logf "@[Sending out %s declaration: %s@." dtid decl;
  output_string !smtin decl; (* TODO: handle errors *)
  predeclared := RegexpSet.add (Str.regexp_string dtid) !predeclared

let smt_init () : unit =
  smtpath :=
    if (!Config.solver_path <> "")
    then !Config.solver_path
    else System.getenv "JSTAR_SMT_PATH";
  if !smtpath = "" then Config.smt_run := false
  else
    try
      begin
        if log log_smt then fprintf logf "@[Initialising SMT@.";
        let args = System.getenv "JSTAR_SMT_ARGUMENTS" in
        let command = Filename.quote !smtpath ^ " " ^ args in
        if log log_phase then
          fprintf logf "@[execute <%s>@]@\n" command;
        let o, i, e = Unix.open_process_full command (environment()) in
        smtout := o;  smtin := i;  smterr := e;
        smtout_lex := Lexing.from_channel !smtout;
        Config.smt_run := true;
        if log log_smt then fprintf logf "@[SMT running.@]";
        output_string i "(set-option :print-success false)\n";
        send_custom_commands ();
	add_native_false ();
	add_native_bitvector_ops ();
	add_native_int_ops ();
	add_native_int_rels ();
	flush i
      end
    with
    | Unix_error(err,f,a) ->
      match err with
      | ENOENT -> fprintf logf "@[@{<b>ERROR:@} Bad path for SMT solver: %s@." a;
                  Config.smt_run := false
      | _ -> raise (Unix_error(err,f,a))


let smt_fatal_recover () : unit  =
  fprintf logf "@[<2>@{<b>SMT ERROR:@}@ ";
  fprintf logf "The SMT solver <%s> stopped unexpectedly.@." !smtpath;
  if log log_smt then
    begin
      fprintf logf "@[Error report from the solver:@.";
      try while true do fprintf logf "@[%s@." (input_line !smterr) done
      with End_of_file -> ()
    end;
  fprintf logf "@[Turning off SMT for this example.@.";
  ignore (Unix.close_process_full (!smtout, !smtin, !smterr));
  print_flush();
  Config.smt_run := false


(* Partition a list into sublists of equal elements *)
let rec equiv_partition
    (eq : 'a -> 'a -> bool)
    (xs : 'a list)
    : 'a list list =
  match xs with
  | x::xs ->
     let (e, xs') = partition (eq x) xs in
     let eqs = equiv_partition eq xs' in
     (x::e) :: eqs
  | [] -> []


(* construct all (unordered) pairs of list elements *)
let rec list_to_pairs
    (xs : 'a list)
    : ('a * 'a) list =
  match xs with
  | x::xs -> (map (fun y -> (x,y)) xs) @ list_to_pairs xs
  | [] -> []


(** feeds the typing context and type unification thingy with info
    gathered from the give args. *)
(* The type inference part is more or less the algorithm W. *)
let rec sexp_of_args = function
  | Arg_var v ->
    let vname = id_munge (Vars.string_var v) in
    let tv = lookup_type vname in
    (vname, tv)
  | Arg_string s ->
    let rxp = (Str.regexp "^\\(-?[0-9]+\\)") in
    let expr =
      if Str.string_match rxp s 0 then
	Str.matched_group 1 s
      else (
	(* if it's not an int that SMT-LIB will recognise, we need to
	   declare it as such (let's pretend strings are ints...) *)
	let scons = id_munge ("string_const_"^s) in
	(* maintain uniqueness of bindings *)
	Hashtbl.replace typing_context scons SType_int;
	scons
      ) in
    (expr, SType_int)
  | Arg_op ("NULL", []) -> ("(_ bv0 64)", SType_bv "64")
  | Arg_op ("numeric_const", [Arg_string(a)]) -> (a, SType_int)
  | Arg_op ("bv_const", [Arg_string(sz); Arg_string(n)]) ->
    (Printf.sprintf "(_ bv%s %s)" n sz, SType_bv sz)
  | Arg_op ("builtin_eq", [a1; a2]) ->
    let (e1, t1) = sexp_of_args a1 in
    let (e2, t2) = sexp_of_args a2 in
    unify t1 t2;
    (Printf.sprintf "(ite (= %s %s) (_ bv1 1) (_ bv0 1))" e1 e2, SType_bv "1")
  | Arg_op ("builtin_neq", [a1; a2]) ->
    let (e1, t1) = sexp_of_args a1 in
    let (e2, t2) = sexp_of_args a2 in
    unify t1 t2;
    (Printf.sprintf "(ite (= %s %s) (_ bv0 1) (_ bv1 1))" e1 e2, SType_bv "1")
  | Arg_op ("bv_const", [Arg_string(sz); Arg_var(v)]) ->
    let vname = id_munge (Vars.string_var v) in
    let tv = lookup_type vname in
    let bv = SType_bv sz in
    unify tv bv;
    (vname, bv)
  | Arg_op (name, args) | Arg_cons (name, args) ->
    let (op_name, op_type, args) = !smtname_and_type_of_op name args in
    let (args_exp, args_types) = sexp_of_args_list args in
    let expr =
      if args = [] then op_name
      else Printf.sprintf "(%s %s)" op_name args_exp in
    let result_type = SType_var (fresh_type_index ()) in
    if name <> "tuple" then
      if args = [] then unify result_type op_type
      else unify op_type (SType_fun (args_types, result_type));
    (expr, result_type)
  | Arg_record fldlist ->
    (* TODO: implement records *)
    ("", SType_var (fresh_type_index ()))
and sexp_of_args_list = function
  | [] -> ("", [])
  | a::al ->
    let (e, t) = sexp_of_args a in
    let (el, tl) = sexp_of_args_list al in
    (" " ^ e ^ el, t::tl)

let sexp_of_eq (a1, a2) =
  let (e1, t1) = sexp_of_args a1 in
  let (e2, t2) = sexp_of_args a2 in
  unify t1 t2;
  Printf.sprintf "(= %s %s)" e1 e2

let sexp_of_neq (a1, a2) =
  let (e1, t1) = sexp_of_args a1 in
  let (e2, t2) = sexp_of_args a2 in
  let t1, t2 = final_type t1, final_type t2 in
  if not (refines t1 t2) && not (refines t2 t1) then
    (* incompatible types! *)
    "true"
  else Printf.sprintf "(distinct %s %s)" e1 e2

let sexp_of_pred = function
  | ("type", (Arg_op ("tuple",[a1; a2]))) ->
    let (_, t1) = sexp_of_args a1 in
    let (_, t2) = sexp_of_args a2 in
    unify t1 t2;
    ("true", SType_bool)
  | (name, (Arg_op ("tuple",args))) ->
    let (pred_name, pred_type, args) = !smtname_and_type_of_op name args in
    let (args_exp, args_types) = sexp_of_args_list args in
    let expr =
      if args = [] then pred_name
      else Printf.sprintf "(%s %s)" pred_name args_exp in
    let result_type = SType_bool in
    if name <> "tuple" then
      if args = [] then unify result_type pred_type
      else unify pred_type (SType_fun (args_types, result_type));
    (expr, result_type)
  | _ -> failwith "TODO"

let rec sexp_of_form ts form =
  let eqs =
    map
      (fun (a1,a2) ->
	(get_pargs_norecs false ts [] a1, get_pargs_norecs false ts [] a2))
      form.eqs in
  let neqs =
    map
      (fun (a1,a2) ->
	(get_pargs_norecs false ts [] a1, get_pargs_norecs false ts [] a2))
      form.neqs in
  let eq_sexp = String.concat " " (map sexp_of_eq eqs) in
  let neq_sexp = String.concat " " (map sexp_of_neq neqs) in
  let disj_list =
    map
      (fun (f1,f2) ->
	let f1s = sexp_of_form ts f1 in
	let f2s = sexp_of_form ts f2 in
	"(or " ^ f1s ^ " " ^ f2s ^ ")")
      form.disjuncts in
  let disj_sexp = String.concat " " disj_list in
  let plain_list =
    map (fun u -> fst (sexp_of_pred u))
      (RMSet.map_to_list form.plain
	 (fun (s,r) -> (s, get_pargs_norecs false ts [] r))) in
  let plain_sexp = String.concat " " plain_list in
  let form_sexp = "(and true "^eq_sexp^" "^neq_sexp^" "^disj_sexp^" "^plain_sexp^")" in
  form_sexp

let decl_sexp_of_typed_id id idt =
  match (final_type idt) with
  | SType_fun (argtl, resl) ->
    Printf.sprintf "(declare-fun %s (%s) %s)"
      id (sexp_of_sort_list argtl) (sexp_of_sort resl)
  | _ ->
    Printf.sprintf "(declare-fun %s () %s)" id (sexp_of_sort idt)


(*** Main SMT IO functions *)

let smt_listen () =
  match Smtparse.main Smtlex.token !smtout_lex with
    | Error e -> raise (SMT_error e)
    | response -> response

let smt_command
    (cmd : string)
    : unit =
  try
    if log log_smt then fprintf logf "@[%s@." cmd;
    print_flush();
    output_string !smtin cmd;
    output_string !smtin "\n";
    flush !smtin;
  with End_of_file | Sys_error _ -> raise SMT_fatal_error

let send_all_types () =
  complete_all_types ();
  let f id idt =
    if not (is_predeclared id) then
      smt_command (decl_sexp_of_typed_id id idt) in
  Hashtbl.iter f typing_context

let smt_assert (ass : string) : unit =
  let cmd = "(assert " ^ ass ^ " )" in
  smt_command cmd;
  smt_onstack := (cmd :: List.hd !smt_onstack) :: List.tl !smt_onstack

let smt_check_sat () : bool =
    try
      let x = Hashtbl.find smt_memo !smt_onstack in
      if log log_smt then fprintf logf "@[[Found memoised SMT call!]@.";
      x
    with Not_found ->
      try
	smt_command "(check-sat)";
	let x = match smt_listen () with
          | Sat -> true
          | Unsat -> false
          | Unknown -> if log log_smt then fprintf logf
              "@[[Warning: smt returned 'unknown' rather than 'sat']@."; true
          | _ -> failwith "TODO" in
	if log log_smt then fprintf logf "@[  %b@." x;
	Hashtbl.add smt_memo !smt_onstack x;
	x
      with End_of_file -> raise SMT_fatal_error

let smt_check_unsat () : bool =
  not (smt_check_sat ())

let smt_push () : unit =
  smt_command "(push)";
  incr smt_fdepth;
  smt_onstack := ([]::!smt_onstack)

let smt_pop () : unit =
  smt_command "(pop)";
  decr smt_fdepth;
  smt_onstack := List.tl !smt_onstack


let smt_reset () : unit =
  for i = 1 to !smt_fdepth do smt_pop () done;
  assert (!smt_fdepth = 0);
  assert (!smt_onstack = [[]])


(** Check whether two sexps are equal under the current assumptions *)
let smt_test_sexp_eq s1 s2 =
  let s = Printf.sprintf "(distinct %s %s)" s1 s2 in
  smt_push();
  smt_assert s;
  let r = smt_check_unsat() in
  smt_pop(); r

let exists_sexp idl sexp =
  let exists_decls =
    fold_left
      (fun s id ->
	Printf.sprintf "%s (%s %s)" s id (sexp_of_sort (lookup_type id)))
      ""
      idl in
  if idl = [] then sexp
  else Printf.sprintf "(exists (%s) %s)" exists_decls sexp

(** try to establish that the pure parts of a sequent are valid using the SMT solver *)
let finish_him
    (ts : term_structure)
    (asm : formula)
    (obl : formula)
    : bool =
  try
    reset_typing_context ();
    let eqs = filter (fun (a,b) -> a <> b) (get_eqs_norecs ts) in
    let neqs = filter (fun (a,b) -> a <> b) (get_neqs_norecs ts) in
    let asm_eq_sexp = String.concat " " (map sexp_of_eq eqs) in
    let asm_neq_sexp = String.concat " " (map sexp_of_neq neqs) in
    let _ = map sexp_of_args (get_args_all ts) in
    let asm_sexp = sexp_of_form ts asm in
    let obl_sexp = sexp_of_form ts obl in
    (* Construct the query *)
    let asm_sexp = "(and true "^asm_eq_sexp^" "^asm_neq_sexp^" "^asm_sexp^") " in
    let rec add_ev_of_form_to_vset form vset =
      let vset_eqneqs =
	fold_left
	  (fun evset (a1,a2) ->
	    let (x, y) =
	      (get_pargs_norecs false ts [] a1, get_pargs_norecs false ts [] a2) in
	    ev_args y (ev_args x evset)
	  )
	  vset
	  (form.eqs@form.neqs) in
      let vset_disjs =
	fold_left
	  (fun evset (f1,f2) ->
	    add_ev_of_form_to_vset f2 (add_ev_of_form_to_vset f1 evset))
	  vset_eqneqs
	  form.disjuncts in
      RMSet.fold_to_list form.plain
	(fun (_,r) evset ->
	  let args = get_pargs_norecs false ts [] r in
	  ev_args args evset)
	vset_disjs in
    let ts_eqneq_vset =
      ev_args_list (let (a,b) = split (eqs@neqs) in a@b) VarSet.empty in
    let left_vset = add_ev_of_form_to_vset asm ts_eqneq_vset in
    let obl_vset = add_ev_of_form_to_vset obl VarSet.empty in
    let evars = VarSet.diff obl_vset left_vset in
    let evars_ids = List.map (fun v -> id_munge (Vars.string_var v))
      (VarSet.elements evars) in

    smt_push(); (* Push a frame to allow reuse of prover *)
    send_all_types ();
    let obl_sexp = exists_sexp evars_ids obl_sexp in
    let query = "(not (=> " ^ asm_sexp ^ obl_sexp ^ "))" in
    smt_assert query;
    (* check whether the forumula is unsatisfiable *)
    let r = smt_check_unsat() in
    smt_pop(); r
  with
  | Type_mismatch (ta, tb) ->
    fprintf logf "@[@{<b>SMT ERROR@}: type mismatch: %a # %a@."
      pp_smt_type ta pp_smt_type tb;
    if log log_smt then dump_typing_context ();
    print_flush();
    false
  | SMT_error r ->
    smt_reset();
    fprintf logf "@[@{<b>SMT ERROR@}: %s@." r;
    if log log_smt then dump_typing_context ();
    print_flush();
    false
  | SMT_fatal_error ->
    smt_fatal_recover();
    if log log_smt then dump_typing_context ();
    false


let true_sequent_smt (seq : sequent) : bool =
  (Clogic.true_sequent seq)
    ||
  (* Call the SMT if the other check fails *)
  (if (not !Config.smt_run) then false
  else
  (Clogic.plain seq.assumption  &&  Clogic.plain seq.obligation
    &&
   ((if log log_smt then fprintf logf "@[Calling SMT to prove@\n %a@." Clogic.pp_sequent seq);
    finish_him seq.ts seq.assumption seq.obligation)))


let frame_sequent_smt (seq : sequent) : bool =
  (Clogic.frame_sequent seq)
    ||
  (if (not !Config.smt_run) then false
  else
  (Clogic.plain seq.obligation
    &&
   ((if log log_smt then fprintf logf "@[Calling SMT to get frame from@\n %a@." Clogic.pp_sequent seq);
    finish_him seq.ts seq.assumption seq.obligation)))


(* Update the congruence closure using the SMT solver *)
let ask_the_audience
    (ts : term_structure)
    (form : formula)
    : term_structure =
  if (not !Config.smt_run) then raise Backtrack.No_match;
  try
    if log log_smt then
      begin
        fprintf logf "@[Calling SMT to update congruence closure@.";
        fprintf logf "@[Current formula:@\n %a@." Clogic.pp_ts_formula (Clogic.mk_ts_form ts form)
      end;
    reset_typing_context ();
    (* Construct equalities and ineqalities from ts *)
    let eqs = filter (fun (a,b) -> a <> b) (get_eqs_norecs ts) in
    let neqs = filter (fun (a,b) -> a <> b) (get_neqs_norecs ts) in
    let ts_eq_sexp = String.concat " " (map sexp_of_eq eqs) in
    let ts_neq_sexp = String.concat " " (map sexp_of_neq neqs) in
    (* get types from ts *)
    let _ = map sexp_of_args (get_args_all ts) in
    let form_sexp = sexp_of_form ts form in
    (* Assert the assumption *)
    let assm_query = "(and true " ^ ts_eq_sexp ^" "^ ts_neq_sexp ^" "^ form_sexp ^ ")" in

    smt_push(); (* Push a frame to allow reuse of prover *)
    (* declare predicates *)
    send_all_types ();
    smt_assert assm_query;
    (* check for a contradiction *)
    if log log_smt then fprintf logf "@[[Checking for contradiction in assumption]@.";
    if smt_check_unsat() then (smt_reset(); raise Assm_Contradiction);
    (* check whether there are any new equalities to find; otherwise raise Backtrack.No_match *)
    let reps = map (fun (t,a) -> (t, sexp_of_args a)) (get_args_rep ts) in
    let req_equiv = map (map fst)
      (equiv_partition (fun x y ->
	let (sx, tx) = snd x in
	let (sy, ty) = snd y in
	(* no need to bother the SMT solver if x and y are of
	   incompatible types. Because we have "completed" all types,
	   compatibility is the same as equality for types *)
	tx = ty && smt_test_sexp_eq sx sy) reps) in
    if for_all (fun ls -> List.length ls = 1) req_equiv then
      (smt_reset(); raise Backtrack.No_match);
    smt_pop();
    (* Update the term structure using the new equalities *)
    fold_left make_list_equal ts req_equiv
  with
  | Type_mismatch (ta, tb) ->
    fprintf logf "@[@{<b>SMT ERROR@}: type mismatch: %a # %a@."
      pp_smt_type ta pp_smt_type tb;
    if log log_smt then dump_typing_context ();
    smt_reset();
    print_flush();
    raise Backtrack.No_match
  | SMT_error r ->
    smt_reset();
    fprintf logf "@[@{<b>SMT ERROR@}: %s@." r;
    print_flush();
    if log log_smt then dump_typing_context ();
    raise Backtrack.No_match
  | SMT_fatal_error ->
    smt_fatal_recover();
    if log log_smt then dump_typing_context ();
    raise Backtrack.No_match

