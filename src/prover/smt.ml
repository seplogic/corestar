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

let predeclared = ref StringSet.empty

let send_custom_commands =
  let decl_re = Str.regexp "[ \t]*([ \t]*declare-fun[ \t]+\\([^ \t()]+\\)" in
  fun () ->
    if !Config.smt_custom_commands <> "" then (
      let cc = open_in !Config.smt_custom_commands in
      try while true do begin
	let cmd = input_line cc in
	if Config.smt_debug() then printf "@[%s@." cmd;
	if Str.string_match decl_re cmd 0 then
	  predeclared := StringSet.add (Str.matched_group 1 cmd) !predeclared;
	output_string !smtin cmd;
	output_char !smtin '\n'
      end done
      with End_of_file -> close_in cc
    )
      
let smt_init () : unit =
  smtpath :=
    if (!Config.solver_path <> "")
    then !Config.solver_path
    else System.getenv "JSTAR_SMT_PATH";
  if !smtpath = "" then Config.smt_run := false
  else
    try
      begin
        if Config.smt_debug() then printf "@[Initialising SMT@.";
        let args = System.getenv "JSTAR_SMT_ARGUMENTS" in
        let command = Filename.quote !smtpath ^ " " ^ args in
        if log log_phase then
          fprintf logf "@[execute <%s>@." command;
        let o, i, e = Unix.open_process_full command (environment()) in
        smtout := o;  smtin := i;  smterr := e;
        smtout_lex := Lexing.from_channel !smtout;
        Config.smt_run := true;
        if Config.smt_debug() then printf "@[SMT running.@.";
        output_string i "(set-option :print-success false)\n";
        send_custom_commands (); flush i
      end
    with
    | Unix_error(err,f,a) ->
      match err with
      | ENOENT -> printf "@[@{<b>ERROR:@} Bad path for SMT solver: %s@." a;
                  Config.smt_run := false
      | _ -> raise (Unix_error(err,f,a))


let smt_fatal_recover () : unit  =
  printf "@[<2>@{<b>SMT ERROR:@}@ ";
  printf "The SMT solver <%s> stopped unexpectedly.@." !smtpath;
  if Config.smt_debug() then
    begin
      printf "@[Error report from the solver:@.";
      try while true do printf "@[%s@." (input_line !smterr) done
      with End_of_file -> ()
    end;
  printf "@[Turning off SMT for this example.@.";
  ignore (Unix.close_process_full (!smtout, !smtin, !smterr));
  print_flush();
  Config.smt_run := false



(* concatenate n instances of string s *)
let rec nstr (s : string) (n : int) : string =
  match n with
  | 0 -> ""
  | _ -> s^(nstr s (n-1))


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


(* This function should be used below to munge all symbols (usually known as
  identifiers). See Section 3.1 of SMT-LIB standard for allowed symbols. *)
(* TODO: Munge keywords such as par, NUMERAL, _, as, let. *)
let id_munge =
  let ok_char = Array.make 256 false in
  let range_ok a z =
    for c = Char.code a to Char.code z do ok_char.(c) <- true done in
  range_ok 'a' 'z'; range_ok 'A' 'Z'; range_ok '0' '9';
  String.iter (fun c -> ok_char.(Char.code c) <- true) "~!@$^&*_+=<>?/-";
  fun s ->
    let n = String.length s in
    let rec ok i = i = n || (ok_char.(Char.code s.[i]) && ok (succ i)) in
    if ok 0 then s else begin
      let r = Buffer.create (n + 2) in
      Buffer.add_char r '|';
      String.iter
        (function '|' -> Buffer.add_string r "PIPE" | c -> Buffer.add_char r c)
        s;
      Buffer.add_char r '|';
      Buffer.contents r
    end


(* Datatype to hold smt type annotations *)

type smt_type =
  | SMT_Var of Vars.var
  | SMT_Pred of string * int
  | SMT_Op of string * int

module SMTTypeSet =
  Set.Make(struct
    type t = smt_type
    let compare = compare
  end)
type smttypeset = SMTTypeSet.t

let smt_union_list (l : smttypeset list) : smttypeset =
  fold_right SMTTypeSet.union l SMTTypeSet.empty

(*
builtin_div
builtin_ge
builtin_gt
builtin_le
builtin_lt
builtin_minus
builtin_plus
*)

let rec args_smttype (arg : Psyntax.args) : smttypeset =
  match arg with
  | Arg_var v -> SMTTypeSet.singleton (SMT_Var(v))
  | Arg_string s ->
          let rxp = (Str.regexp "^\\(-?[0-9]+\\)") in
          if Str.string_match rxp s 0 then SMTTypeSet.empty
          else SMTTypeSet.singleton (SMT_Op("string_const_"^s, 0))
  | Arg_op ("builtin_plus",args) -> smt_union_list (map args_smttype args)
  | Arg_op ("builtin_minus",args) -> smt_union_list (map args_smttype args)
  | Arg_op ("builtin_mult",args) -> smt_union_list (map args_smttype args)
  | Arg_op ("numeric_const", [Arg_string(a)]) -> SMTTypeSet.empty
  | Arg_op (name, args) ->
          let s = SMTTypeSet.singleton (SMT_Op(("op_"^name), (length args))) in
          smt_union_list (s::(map args_smttype args))
  | Arg_cons (name, args) -> smt_union_list (map args_smttype args)
  | Arg_record fldlist -> SMTTypeSet.empty


(* Functions to convert various things to sexps & get types *)

let rec string_sexp_args (arg : Psyntax.args) : string =
  match arg with
  | Arg_var v -> id_munge(Vars.string_var v)
  | Arg_string s ->
          let rxp = (Str.regexp "^\\(-?[0-9]+\\)") in
          if Str.string_match rxp s 0 then (Str.matched_group 1 s)
          else id_munge("string_const_"^s)

  | Arg_op ("builtin_plus",[a1;a2]) ->
          Printf.sprintf "(+ %s %s)" (string_sexp_args a1) (string_sexp_args a2)
  | Arg_op ("builtin_minus",[a1;a2]) ->
          Printf.sprintf "(- %s %s)" (string_sexp_args a1) (string_sexp_args a2)
  | Arg_op ("builtin_mult",[a1;a2]) ->
          Printf.sprintf "(* %s %s)" (string_sexp_args a1) (string_sexp_args a2)
  | Arg_op ("numeric_const", [Arg_string(a)]) -> a
  | Arg_op (name,[]) -> id_munge ("op_"^name)
  | Arg_op (name,args) ->
          Printf.sprintf "(%s %s)" (id_munge("op_"^name)) (string_sexp_args_list args)
  | Arg_record _ -> ""  (* shouldn't happen as converted to preds *)
  | Arg_cons _ -> failwith "TODO: Smt.string_sexp_args"
and string_sexp_args_list (argsl : Psyntax.args list) : string =
  match argsl with
  | [] -> ""
  | a::al -> (string_sexp_args a) ^ " " ^ (string_sexp_args_list al)


let string_sexp_eq (a : Psyntax.args * Psyntax.args) : string =
  match a with (a1, a2) ->
  Printf.sprintf "(= %s %s)" (string_sexp_args a1) (string_sexp_args a2)


let string_sexp_neq (a : Psyntax.args * Psyntax.args) : string =
  match a with a1, a2 ->
  Printf.sprintf "(distinct %s %s)" (string_sexp_args a1) (string_sexp_args a2)


let string_sexp_pred (p : string * Psyntax.args) : (string * smttypeset) =
  match p with
  | ("GT",(Arg_op ("tuple",[a1;a2]))) ->
      (Printf.sprintf "(> %s)" (string_sexp_args_list [a1;a2]), SMTTypeSet.empty)

  | ("LT",(Arg_op ("tuple",[a1;a2]))) ->
      (Printf.sprintf "(< %s)" (string_sexp_args_list [a1;a2]), SMTTypeSet.empty)

  | ("GE",(Arg_op ("tuple",[a1;a2]))) ->
      (Printf.sprintf "(>= %s)" (string_sexp_args_list [a1;a2]), SMTTypeSet.empty)

  | ("LE",(Arg_op ("tuple",[a1;a2]))) ->
      (Printf.sprintf "(<= %s)" (string_sexp_args_list [a1;a2]), SMTTypeSet.empty)

  | (name, args) ->
    let name = id_munge("pred_"^name) in
    match args with
      | Arg_op ("tuple",al) ->
          let types = SMTTypeSet.add (SMT_Pred(name,(length al))) (args_smttype args) in
          ((if al = [] then name else
            Printf.sprintf "(%s %s)" name (string_sexp_args_list al)),
          types)
      | _ -> failwith "TODO: Smt.string_sexp_pred"


let rec string_sexp_form
    (ts : term_structure)
    (form : formula)
    : (string * smttypeset) =
  (* Construct equalities and inequalities *)
  let eqs = map (fun (a1,a2) -> ((get_pargs_norecs false ts [] a1),
                                   (get_pargs_norecs false ts [] a2))) form.eqs in
  let neqs = map (fun (a1,a2) -> ((get_pargs_norecs false ts [] a1),
                                    (get_pargs_norecs false ts [] a2))) form.neqs in
  let eq_sexp = String.concat " " (map string_sexp_eq eqs) in
  let neq_sexp = String.concat " " (map string_sexp_eq neqs) in

  let eqneqs = (let a,b = split (eqs@neqs) in a@b) in
  let eq_types = smt_union_list (map args_smttype eqneqs) in

  let disj_list, disj_type_list =
     split (map (fun (f1,f2) ->
                  let f1s, f1v = string_sexp_form ts f1 in
                  let f2s, f2v = string_sexp_form ts f2 in
                  ( "(or " ^ f1s ^ " " ^ f2s ^ ")",
                    SMTTypeSet.union f1v f2v ) ) form.disjuncts) in
  let disj_sexp = String.concat " " disj_list in
  let disj_types = smt_union_list disj_type_list in

  let plain_list, plain_type_list =
     split ( map string_sexp_pred
            ( RMSet.map_to_list form.plain
            (fun (s,r) -> (s, get_pargs_norecs false ts [] r)))) in
  let plain_sexp = String.concat " " plain_list in

  let plain_types = smt_union_list plain_type_list in

  let types = smt_union_list [eq_types; disj_types; plain_types] in

  let form_sexp = "(and true " ^ eq_sexp ^ " " ^ neq_sexp ^ " " ^
                                 disj_sexp ^ " " ^ plain_sexp ^ ")"  in
  (form_sexp, types)


let string_sexp_decl (t : smt_type) : string =
  match t with
  | SMT_Var v ->
      Printf.sprintf "(declare-fun %s () Int)" (id_munge (Vars.string_var v))
  | SMT_Pred (s,i)
      -> Printf.sprintf "(declare-fun %s (%s) Bool)" (id_munge s) (nstr "Int " i)
  | SMT_Op (s,i)
      -> Printf.sprintf "(declare-fun %s (%s) Int)" (id_munge s) (nstr "Int " i)


(* Main SMT IO functions *)

let smt_listen () =
  match Smtparse.main Smtlex.token !smtout_lex with
    | Error e -> raise (SMT_error e)
    | response -> response

let smt_command
    (cmd : string)
    : unit =
  try
    if Config.smt_debug() then printf "@[%s@." cmd;
    print_flush();
    output_string !smtin cmd;
    output_string !smtin "\n";
    flush !smtin;
  with End_of_file | Sys_error _ -> raise SMT_fatal_error

let send_types types =
  let name = function
    | SMT_Var v -> Vars.string_var v
    | SMT_Pred (n, _)
    | SMT_Op (n, _) -> n in
  let f x =
    if not (StringSet.mem (name x) !predeclared) then
      smt_command (string_sexp_decl x) in
  SMTTypeSet.iter f types

let smt_assert (ass : string) : unit =
  let cmd = "(assert " ^ ass ^ " )" in
  smt_command cmd;
  smt_onstack := (cmd :: List.hd !smt_onstack) :: List.tl !smt_onstack

let smt_check_sat () : bool =
    try
      let x = Hashtbl.find smt_memo !smt_onstack in
      if Config.smt_debug() then printf "@[[Found memoised SMT call!]@.";
      x
    with Not_found ->
      smt_command "(check-sat)";
      let x = match smt_listen () with
        | Sat -> true
        | Unsat -> false
        | Unknown -> if Config.smt_debug() then printf
          "@[[Warning: smt returned 'unknown' rather than 'sat']@."; true
        | _ -> failwith "TODO: Smt.smt_check_sat" in
      if Config.smt_debug () then printf "@[  %b@." x;
      Hashtbl.add smt_memo !smt_onstack x;
      x

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


(* Check whether two args are equal under the current assumptions *)
let smt_test_eq (a1 : Psyntax.args) (a2 : Psyntax.args) : bool =
  smt_push();
  smt_assert (string_sexp_neq (a1,a2));
  let r = smt_check_unsat() in
  smt_pop(); r

let decl_evars (types : smttypeset) (s : string) : string =
  let v2s = function
    | SMT_Var v when Vars.is_evar v ->
        "(" ^ id_munge (Vars.string_var v) ^ " Int)"
    | _ -> "" in
  let prefix = SMTTypeSet.fold (fun v p -> v2s v ^ p) types "" in
  if prefix = "" then s else "(exists (" ^ prefix ^ ") " ^ s ^ ")"

(* try to establish that the pure parts of a sequent are valid using the SMT solver *)
let finish_him ts asm obl =
  try
    (* Push a frame to allow reuse of prover *)
    smt_push();

    (* Construct equalities and ineqalities from ts *)
    let eqs = filter (fun (a,b) -> a <> b) (get_eqs_norecs ts) in
    let neqs = filter (fun (a,b) -> a <> b) (get_neqs_norecs ts) in
    let asm_eq_sexp = String.concat " " (map string_sexp_eq eqs) in
    let asm_neq_sexp = String.concat " " (map string_sexp_neq neqs) in

    let ts_types = smt_union_list (map args_smttype (get_args_all ts)) in

    let ts_eqneq_types = smt_union_list
      (map (fun (a,b) -> SMTTypeSet.union (args_smttype a) (args_smttype b)) (eqs @ neqs)) in

    (* Construct sexps and types for assumption and obligation *)
    let asm_sexp, asm_types = string_sexp_form ts asm in
    let obl_sexp, obl_types = string_sexp_form ts obl in

    let types = smt_union_list [ts_types; asm_types; obl_types] in

    (* declare variables and predicates *)
    send_types types;
(*     SMTTypeSet.iter (fun x -> ignore (smt_command (string_sexp_decl x)))
types; *)

    (* Construct and run the query *)
    let asm_sexp = "(and true " ^ asm_eq_sexp ^ " " ^ asm_neq_sexp ^ " " ^ asm_sexp ^ ") " in
    let obl_sexp =
      decl_evars
        (SMTTypeSet.diff obl_types (SMTTypeSet.union ts_eqneq_types asm_types))
        obl_sexp in
    let query = "(not (=> " ^ asm_sexp ^ obl_sexp ^ "))"
    in smt_assert query;

    (* check whether the forumula is unsatisfiable *)
    let r = smt_check_unsat() in
    smt_pop(); r
  with
  | SMT_error r ->
    smt_reset();
    printf "@[@{<b>SMT ERROR@}: %s@." r;
    print_flush();
    false
  | SMT_fatal_error ->
    smt_fatal_recover();
    false


let true_sequent_smt (seq : sequent) : bool =
  (Clogic.true_sequent seq)
    ||
  (* Call the SMT if the other check fails *)
  (if (not !Config.smt_run) then false
  else
  (Clogic.plain seq.assumption  &&  Clogic.plain seq.obligation
    &&
   ((if Config.smt_debug() then printf "@[Calling SMT to prove@\n %a@." Clogic.pp_sequent seq);
    finish_him seq.seq_ts seq.assumption seq.obligation)))


let frame_sequent_smt seq =
  Clogic.frame_sequent seq
  || ( not !Config.smt_run
     && Clogic.plain seq.obligation
     && (if Config.smt_debug () then
          printf "@[Calling SMT to get frame from@\n %a@." Clogic.pp_sequent seq;
        finish_him seq.seq_ts seq.assumption seq.obligation))

(* Update the congruence closure using the SMT solver *)
let ask_the_audience
    (ts : term_structure)
    (form : formula)
    : term_structure =
  if (not !Config.smt_run) then raise Backtrack.No_match
  else try
    if Config.smt_debug() then
      begin
        printf "@[Calling SMT to update congruence closure@.";
        printf "@[Current formula:@\n %a@." Clogic.pp_ts_formula (Clogic.mk_ts_form ts form)
      end;

    smt_push();

    (* Construct equalities and ineqalities from ts *)
    let eqs = filter (fun (a,b) -> a <> b) (get_eqs_norecs ts) in
    let neqs = filter (fun (a,b) -> a <> b) (get_neqs_norecs ts) in
    let ts_eq_sexp = String.concat " " (map string_sexp_eq eqs) in
    let ts_neq_sexp = String.concat " " (map string_sexp_neq neqs) in

    let ts_types = smt_union_list (map args_smttype (get_args_all ts)) in

    (* Construct sexps and types for assumption and obligation *)
    let form_sexp, form_types = string_sexp_form ts form in

    let types = smt_union_list [ts_types; form_types] in

    (* declare predicates *)
    send_types types;
(*     SMTTypeSet.iter (fun x -> ignore(smt_command (string_sexp_decl x)))
types; *)

    (* Assert the assumption *)
    let assm_query = "(and true " ^ ts_eq_sexp ^" "^ ts_neq_sexp ^" "^ form_sexp ^ ")"
    in smt_assert assm_query;

    (* check for a contradiction *)
    if Config.smt_debug() then printf "@[[Checking for contradiction in assumption]@.";
    if smt_check_unsat() then (smt_reset(); raise Assm_Contradiction);

    (* check whether there are any new equalities to find; otherwise raise Backtrack.No_match *)
    (*
    if Config.smt_debug() then printf "[Checking for new equalities]@\n";
    smt_push();
    let reps = get_args_rep ts in
    let rep_sexps = String.concat " " (map (fun (x,y) -> string_sexp_neq (snd x,snd y))
                                                (list_to_pairs reps) )
    in
    smt_assert ( "(and true " ^ rep_sexps ^ " )" );
    if smt_check_sat() then (smt_reset(); raise Backtrack.No_match);
    smt_pop();
    *)
    (* Update the term structure using the new equalities *)
    let reps = get_args_rep ts in
    let req_equiv = map (map fst)
                        (equiv_partition (fun x y -> smt_test_eq (snd x) (snd y)) reps)
    in
    if for_all (fun ls -> List.length ls = 1) req_equiv then
      (smt_reset(); raise Backtrack.No_match);
    smt_pop();
    fold_left make_list_equal ts req_equiv
  with
  | SMT_error r ->
    smt_reset();
    printf "@[@{<b>SMT ERROR@}: %s@." r;
    print_flush();
    raise Backtrack.No_match
  | SMT_fatal_error ->
    smt_fatal_recover();
    raise Backtrack.No_match

