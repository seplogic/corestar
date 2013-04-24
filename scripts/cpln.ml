(* Same as "ln -s $(readlink -e $1) $2" on Ubuntu, because finding a command
that does the same on both Ubuntu and Mac is incredibly annoying. *)

open Format

module F = Filename
module U = Unix
module S = Set.Make (String)

exception Bad_link of string
exception Cycle of string

let ( / ) = F.concat

let canonicalize d f = if F.is_relative f then F.concat d f else f

let readlink =
  let rec f seen x =
    if not (Sys.file_exists x) then raise (Bad_link x);
    if S.mem x seen then raise (Cycle x);
    try f (S.add x seen) (canonicalize (F.dirname x) (U.readlink x))
    with U.Unix_error (U.EINVAL, "readlink", _) -> x in
  f S.empty

let () =
  if Array.length Sys.argv != 3 then exit 1;
  try
    let src = readlink (canonicalize (Sys.getcwd ()) Sys.argv.(1)) in
    let tgt = Sys.argv.(2) in
    let tgt =
      if Sys.file_exists tgt && Sys.is_directory tgt
      then tgt/(F.basename src)
      else tgt in
    if Sys.file_exists tgt then U.unlink tgt;
    U.handle_unix_error (U.symlink src) tgt
  with
    | Bad_link x -> eprintf "@[%s: missing file@." x
    | Cycle x -> eprintf "@[%s: cyclic symbolic link@." x

