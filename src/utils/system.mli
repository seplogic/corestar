(********************************************************
   This file is part of coreStar
        src/utils/system.mli
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   coreStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)


(** The delimiter used in CLASSPATH, SOURCEPATH, ... by Java. *)
val java_path_delimiter : string
val java_path_delimiter_re : Str.regexp

(**
  [getenv v] returns the value in the system environment of the variable
  [v], or the empty string if [v] is not set.
 *)
val getenv : string -> string

(**
  [getenv_dirlist v] assumes [v] is a something like PATH and splits its
  value (if set) into a list. This function does NOT process trailing '*',
  nor does it filter out stuff that is usually ignored by classpaths, see:
    http://download.oracle.com/javase/6/docs/technotes/tools/index.html#classpath
  Leading, trailing, and repeated delimiters ARE ignored, see
    http://bugs.sun.com/bugdatabase/view_bug.do?bug_id=4809833
 *)
val getenv_dirlist : string -> string list

(** [string_of_file f] returns the content of file [f] as a string *)
val string_of_file : string -> string

(**
  [parse_file parser lexer fname ftype] parses [fname] using the given
  [parser] and [lexer], prints some standard messages, and returns the
  result of the parser. ['a] is the token type, ['b] is the type of the
  parsing result.
 *)
val parse_file :
  ((Lexing.lexbuf->'a) -> Lexing.lexbuf -> 'b) ->
  (Lexing.lexbuf->'a) ->
  string -> string -> 'b

(**
  [find_file_from_dirs dirs f] tries to find file [f] (possibly a directory)
  in the current directory and then in [dirs]. Returns the first location
  of [f]. Raises [Not_found] if not found. The behavior is undefined
  if [f] is an absolute path.
 *)
val find_file_from_dirs : string list -> string -> string

(**
  [fs_postorder m f] runs [m f'] for all files [f'] reachable by descending
  directories from [f], and does so in postorder. (For the purposes of this
  description directories are files.)
 *)
val fs_postorder : (string -> unit) -> string -> unit

(**
  [fs_filter predicate directory] returns a list of paths under [directory]
  that satisfy [predicate].
 *)
val fs_filter : (string -> bool) -> string -> string list

(** [rm_rf f] is the same as the shell command <tt>rm -rf f</tt>. *)
val rm_rf : string -> unit

(** [mkdir_p d] is the same as the shell command <tt>mkdir -p d</tt>. *)
val mkdir_p : string -> unit

(**
  [is_executable_available f] returns whether [f] is in the PATH, not a
  directory, and executable.
 *)
val is_executable_available : string -> bool

(**
  [is_ext_file ext f] says whether file [f] is a normal file with a name
  ending in [ext]. It is case insensitive.
 *)
val is_file : string -> string -> bool

(** Ignores signals that shouldn't stop corestar. *)
val set_signal_handlers : unit -> unit

val terminal_red : string
val terminal_green : string
val terminal_white : string
