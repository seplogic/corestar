(********************************************************
   This file is part of coreStar
        src/utils/debug.ml
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   coreStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)

(*
 * Debug helpers. The code of coreStar supports debugging in two ways. First, by
 * setting [safe] mode (possibly expensive) sanity checks are run. (There is no
 * reason to ever turn off cheap sanity checks.) Second, the code is
 * interspersed with dumps of various state information. For logging, however,
 * there can't be only one control that turns it on or off, because that would
 * be confusing. For example, if the programmer suspects a bug in the proof
 * search, then messages that describe how symbolic execution proceeds are
 * distracting garbage.  Hence, logging is split into categories, and each
 * subset of categories may be turned on at a time. As with sanity checks,
 * logging may be expensive, so the messages for categories that are turned off
 * are not even constructed (rather than being constructed but not printed).
 *
 * When sanity check or logging is turned off, the compiler throws away the
 * corresponding debugging code completely. That is why the on/off controls are
 * immutable and why bit-masks are used instead of fancier data structures like
 * lists.
 *
 * Guidelines for sanity checks. Expensive sanity (invariant) checks should
 * typically be put in functions starting with "check_". Then they should be
 * called by using the laziness of the if statement and that of boolean and.
 *    if safe then check_inv data
 * The checking function is suposed to raise an exception or to assert if a
 * problem is detected.
 *
 * Guidelines for logging. The typical logging code is
 *    if log log_category then
 *      fprintf logf "Some message.@\n"
 * assuming that modules Debug and Format are open. Note that each log message
 * starts by opening a box ("@[") and finishes by flushing, closing boxes and
 * going to a new line ("@."). The first complication that may appear is that
 * a message belongs not to one log_category but to several log categories
 * log_a, log_b, and log_c.
 *    if log_active land (log_a lor log_b lor log_c) <> 0 then
 *      fprintf logf "Some message.@\n"
 * The second complication is that the message might be long.
 *    if log log_category then
 *      fprintf logf "@[<2>Some message with@ break hints.@]@\n"
 * Finally, to dump big data structures use %a.
 *    if log log_category then
 *      fprintf logf "@[<2>Here's a foo:%a@]@\n" print_function data
 * Note that while printing a hierarchical structure it is usually convenient to
 * (1) force a newline "@\n", (2) open a box and prepare the indent for the
 * children "@[<2>", (3) print some data, (4) recursively print the children
 * using %a, and (5) close the box "@]". Boxes should typically be opened only
 * after "@\n". A data type X should have a pretty printing function
 *    pp_X : X Corestar_std.pretty_printer
 *
 * Opening Format should make it less likely to mix Format with Printf.
 *
 * Wrap the main function with
 *    fprintf logf "@["; ...; fprintf logf "@]@?"
 *
 * Finally, don't forget that guidelines are meant to be broken.
 *)

open Corestar_std
open Format

let safe = true

let log_exec = 1 lsl 0
let log_load = 1 lsl 1
let log_logic = 1 lsl 2
let log_phase = 1 lsl 3
let log_prove = 1 lsl 4
let log_specs = 1 lsl 5
let log_smt = 1 lsl 6

(* enable html tags in output *)
let log_html = false

let log_active = log_phase lor log_smt lor log_exec lor log_prove
  (* -1 means all, 0 means one, in general use lor *)

let log x = log_active land x <> 0

let logf = std_formatter

let add_formatter_tag formatter (tag, start, stop) =
  let fs = pp_get_formatter_tag_functions formatter () in
  let add s f t = if t = tag then s else f t in
  pp_set_formatter_tag_functions formatter
    { fs with
      mark_open_tag = add start fs.mark_open_tag
    ; mark_close_tag = add stop fs.mark_close_tag }

let () =
  let tags =
    [ "dotpdf"
      , "<a href =\""
      , ".pdf\" title=\"pdf may need to be created with dot\">link</a>"
    ; "css"
      , "<link rel=\"stylesheet\" type=\"test/css\" href=\"..\\..\\..\\log.css\" title=\"Default\"/>"
      , ""
    ; "encoding"
      , "<meta http-equiv=\"Content-Type\" content=\"text/html; charset=utf-8\"/>"
      , "" ] in
  let html_tags =
    [ "details"; "h1"; "h2"; "h3"; "h4"; "p"; "summary" ]
    @ List.map (fun (t, _, _) -> t) tags in
  if log_html then begin
    List.iter (add_formatter_tag std_formatter) tags;
    set_tags true
  end else begin
    let disable t = add_formatter_tag std_formatter (t, "", "") in
    List.iter disable html_tags
  end

(* {2} Profiling helpers *) (* {{{ *)

let prof_time = ref 0.0
let prof_phase = ref "init"
let prof_phase m =
  if log log_phase then begin
    let t = Sys.time () in
    fprintf logf "@[... phase %s done in %.1f s@." !prof_phase (t -. !prof_time);
    fprintf logf "@[start phase %s@." m;
    prof_time := t;
    prof_phase := m
  end

let prof_time_of_c = Hashtbl.create 0
let prof_start_of_c = Hashtbl.create 0
let prof_start c =
  assert (not (Hashtbl.mem prof_start_of_c c));
  Hashtbl.replace prof_start_of_c c (Sys.time ())
let prof_stop c =
  let t2 = Sys.time () in
  let t1 = Hashtbl.find prof_start_of_c c in
  Hashtbl.remove prof_start_of_c c;
  let ts = (try Hashtbl.find prof_time_of_c c with Not_found -> []) in
  Hashtbl.replace prof_time_of_c c (t2 -. t1 :: ts)
let prof_pp_stats () =
  let stats =
    let sum = List.fold_left (+.) 0.0 in
    [ (* "times", pp_list_sep " " pp_float
    ; *) "max", List.fold_left max 0.0
    ; "total", sum
    ; "cnt", float_of_int @@ List.length
    ; "avg", (fun ts -> sum ts /. float_of_int (List.length ts))
    ] in
  let pp (n, f) c ts = fprintf logf "@[<2>%s %s %a@]@\n" c n f ts in
  let pp_categ (n, f) =
    let xs = Hashtbl.fold (fun c ts xs -> (f ts, c) :: xs) prof_time_of_c [] in
    let xs = List.sort compare xs in
    List.iter (fun (v, c) -> fprintf logf "%s %s %.03f@\n" n c v) xs;
    fprintf logf "@\n" in
  List.iter pp_categ stats
let prof_fun1 c f x = prof_start c; let r = f x in prof_stop c; r
let prof_fun2 c f x y = prof_start c; let r = f x y in prof_stop c; r
let prof_fun3 c f x y z = prof_start c; let r = f x y z in prof_stop c; r

(* }}} *)
