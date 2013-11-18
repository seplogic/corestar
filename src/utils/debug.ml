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

open Format

let safe = true

let log_exec = 1 lsl 0
let log_load = 1 lsl 1
let log_logic = 1 lsl 2
let log_phase = 1 lsl 3
let log_prove = 1 lsl 4
let log_specs = 1 lsl 5
let log_cfg = 1 lsl 6
let log_mm = 1 lsl 7
let log_cc = 1 lsl 8
let log_smt = 1 lsl 9

(* enable (html-)tags in output *)
let log_html = false

let log_active = log_phase lor log_exec lor log_smt
  (* -1 means all, 0 means one, in general use lor *)

let () = if log_html then set_tags true

let log x = log_active land x <> 0

let logf = std_formatter

let () =
  let ftfs = get_formatter_tag_functions () in
  set_formatter_tag_functions
    { ftfs with 
      mark_open_tag =
	(function
	  | "dotpdf" -> "<a href =\""
	  | "css" -> "<link rel=\"stylesheet\" type=\"test/css\" href=\"..\\..\\..\\log.css\" title=\"Default\"/>"
	  | t -> ftfs.mark_open_tag t)
    ; mark_close_tag =
	(function
	  | "dotpdf" -> ".pdf\" title=\"pdf may need to be created with dot\">link</a>"
	  | "css" -> ""
	  | t -> ftfs.mark_close_tag t)
    }

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

(* }}} *)
