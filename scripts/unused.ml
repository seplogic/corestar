(** Finds stuff declared in mli that is not used in *other* ml-s. *)

open Format

type file_info = {
  path : string;
  declarations : string list; (* ids appearing in mli *)
  uses : string list (* ids appearing in ml *)
}

let list_of_hashtbl h = Hashtbl.fold (fun x () xs -> x :: xs) h []

let get_ids fn lexer =
  let h = Hashtbl.create 101 in
  try
    let c = open_in fn in
    let lb = Lexing.from_channel (open_in fn) in
    lexer h lb;
    let r = list_of_hashtbl h in
    close_in c;
    r
  with Sys_error _ ->
    printf "@[Warning: missing %s@." fn; []

let parse fn = {
  path = fn;
  declarations = get_ids (fn ^ "i") Id_extractor.id_decl;
  uses = get_ids fn Id_extractor.id
}

module StringSet = Set.Make (String)

let () =
  let fis =
    Utils.files_map (fun x->Filename.check_suffix x ".ml") parse "src" in
  let fis =
    Utils.files_map
      (fun x->Filename.check_suffix x ".mly" || Filename.check_suffix x ".mll")
      (fun fn->{path=fn;declarations=[];uses=get_ids fn Id_extractor.id})
      "src"
    @ fis in
  let h1 = Hashtbl.create 10007 in
  let h2 = Hashtbl.create 10007 in
  let add_use u =
    if not (Hashtbl.mem h2 u) then
      begin
        if not (Hashtbl.mem h1 u) then
          Hashtbl.add h1 u ()
        else
          begin
            Hashtbl.remove h1 u;
            Hashtbl.add h2 u ()
          end
      end in
  List.iter (fun {uses=uses;declarations=_;path=_} -> List.iter add_use uses) fis;
  let process {path=path; declarations=declarations; uses=_} =
    let bd = List.fold_left
      (fun s d -> if Hashtbl.mem h1 d then StringSet.add d s else s)
      StringSet.empty
      declarations in
    if not (StringSet.is_empty bd) then
    begin
      printf "@\n@[<4>%si@\n" path;
      StringSet.iter (fun x -> printf "%s@\n" x) bd;
      printf "@]"
    end in
  printf "@[";
  List.iter process fis;
  printf "@."

