(********************************************************
   This file is part of coreStar
        src/utils/system.ml
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   coreStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)

open Debug
open Corestar_std
open Format

let java_path_delimiter = if Sys.os_type = "Windows" then ";" else ":"
let java_path_delimiter_re = Str.regexp (java_path_delimiter ^ "+")

let getenv variable =
  try Sys.getenv variable with Not_found -> ""

let getenv_dirlist variable =
  Str.split java_path_delimiter_re (getenv variable)


(* read a file into a string *)
let string_of_file fname =
  let ichan = if fname = "-" then stdin else open_in fname
  and str = Bytes.create 1024
  and buf = Buffer.create 1024 in
  let rec loop () =
    let len = input ichan str 0 1024 in
    Buffer.add_substring buf str 0 len;
    if len = 0 then Buffer.contents buf else loop () in
  let s = loop () in
  close_in ichan;
  s


let parse_file pars lexe fname ftype =
  try
    if log log_phase then printf "begin parsing %s from %s@\n" ftype fname;
    let ichan = open_in fname in
    let ret = pars lexe (Lexing.from_channel ichan) in
    Parsing.clear_parser ();
    close_in ichan;
    if log log_phase then printf "end parsing %s from %s@\n" ftype fname;
    ret
  with
    | Parsing.Parse_error ->
        eprintf "@{<b>E: %s:@} parse error@." fname; exit 1

(*
  Check if file exists in current directory, or in list of directories supplied.
  Returns full filename if found,
  If not raises Not_found
*)
let find_file_from_dirs dirs fname =
  if Sys.file_exists fname then fname
  else
    let f x = Filename.concat x fname in
    f (List.find (function d -> Sys.file_exists (f d)) dirs)

let rec fs_postorder m f =
  if Sys.file_exists f then begin
    if Sys.is_directory f then begin
      let children = Array.map (Filename.concat f) (Sys.readdir f) in
      Array.iter (fs_postorder m) children
    end;
    m f
  end

let fs_filter p f =
  let r = ref [] in
  fs_postorder (fun x -> if p x then r =:: x) f; !r

let rm_rf f =
  fs_postorder
    (fun x -> if Sys.is_directory x then Unix.rmdir x else Unix.unlink x) f

let rec mkdir_p dir =
  if Sys.file_exists dir then begin
    if not (Sys.is_directory dir) then
      raise (Unix.Unix_error (Unix.EEXIST, "mkdir_p", dir))
  end else begin
    mkdir_p (Filename.dirname dir);
    Unix.mkdir dir 0o755
  end

let is_executable_available fn =
  try
    let candidate = find_file_from_dirs (getenv_dirlist "PATH") fn in
    Unix.access candidate [Unix.X_OK; Unix.R_OK];
    true
  with _ -> false

let is_file ext fn =
  Sys.file_exists fn && not (Sys.is_directory fn) &&
  StringH.ends_with (String.lowercase ext) (String.lowercase fn)

let set_signal_handlers () =
  let old = Sys.signal Sys.sigpipe Sys.Signal_ignore in
  assert (old = Sys.Signal_default)

(* TODO(rgrig): Thee should probably depend on the terminal. *)
(* TODO(rgrig): Is there a (nice) ncurses ocaml inerface? *)
let terminal_red = "\x1B[1;31m"
let terminal_green = "\x1B[1;32m"
let terminal_white = "\x1B[0m"

