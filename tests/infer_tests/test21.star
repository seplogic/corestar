//  1 -> 2: a
//  1 -> 1: a, b, c
//  2 -> 1: b
//  2 -> 2: a, c
//  2 -> 3: b
//  3 -> 3: a, b, c

procedure a:
  { $gs=1 } ($gs) { $gs=1 || $gs=2 }
  { $gs!=1 } () { } // $gs not modified

procedure b:
  { $gs=2 } ($gs) { $gs=1 || $gs=3 }
  { $gs!=2 } () {}

procedure c:
  {} () {} // quite irrelevant to the automaton

// one step
procedure run_a: ? call a();
procedure run_b: ? call b();
procedure run_c: ? call c();

// two steps
procedure run_aa: ? call a(); call a(); // same as one a()
procedure run_ab: ? call a(); call b(); // 1->1,3; 2->1,3; 3->3
procedure run_ac: ? call a(); call c(); // same as one a()
procedure run_ba: ? call b(); call a(); // 1->1,2; 2->1,2,3; 3->3
procedure run_bb: ? call b(); call b(); // same as one b()
procedure run_bc: ? call b(); call c(); // same as one b()
procedure run_ca: ? call c(); call a(); // same as one a()
procedure run_cb: ? call c(); call b(); // same as one b()
procedure run_cc: ? call c(); call c(); // same as one c()

// three steps
// TODO
