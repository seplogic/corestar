type 'a t = ('a, unit) Hashtbl.t

let add h e = Hashtbl.replace h e ()

let remove h e = Hashtbl.remove h e

let create = Hashtbl.create

let singleton e =
  let h = create 13 in
  add h e; h

let mem = Hashtbl.mem

let elements h =
  Hashtbl.fold (fun x _ xs -> x :: xs) h []

exception X
let choose h =
  let r = ref None in
  try Hashtbl.iter (fun x _ -> r := Some x; raise X) h; raise Not_found
  with X -> (match !r with Some x -> x | _ -> failwith "impossible")

let iter f h = Hashtbl.iter (fun x _ -> f x) h

let fold f h z = Hashtbl.fold (fun x _ r -> f x r) h z

let length h = Hashtbl.length h
