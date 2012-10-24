type 'a t = 'a HashSet.t

let create = HashSet.create

let singleton = HashSet.singleton

let add work_set done_set w =
  if HashSet.mem done_set w then ()
  else HashSet.add work_set w

let perform_work work_set f =
  let done_set = HashSet.create 1 in
  try while true do
    let current = HashSet.choose work_set in
    HashSet.remove work_set current;
    HashSet.add done_set current;
    f (add work_set done_set) current
  done
  with Not_found -> ()
