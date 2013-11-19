// Tests for angelic-vs-demonic splits.

// Should infer: { @parameter0: == 4 } { $ret_v0 == 5 || $ret_v0 == 6 }
procedure OneDemonicSplit:
?
  goto l1, l2, l3;
  label l1; call $ret_v0 := p1(@parameter0:); goto done;
  label l2; call $ret_v0 := p2(@parameter0:); goto done;
  label l3; call $ret_v0 := p3(@parameter0:); goto done;
  label done;

// Should infer the same as for p123.
procedure OneAngelicSplit:
?
  call $ret_v0 := p123(@parameter0:);

procedure p1: { @parameter0: = 1 || @parameter0: = 4 }(){ $ret_v0 = 5 }
procedure p2: { @parameter0: = 2 || @parameter0: = 4 }(){ $ret_v0 = 5 }
procedure p3: { @parameter0: = 3 || @parameter0: = 4 }(){ $ret_v0 = 6 }
procedure p123:
  { @parameter0: = 1 || @parameter0: = 4 } () { $ret_v0 = 5 }
  { @parameter0: = 2 || @parameter0: = 4 } () { $ret_v0 = 5 }
  { @parameter0: = 3 || @parameter0: = 4 } () { $ret_v0 = 6 }
