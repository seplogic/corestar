// Tests for angelic-vs-demonic splits.

// Should infer: { %x == 4 } { %y == 5 || %y == 6 }
procedure (%y) := OneDemonicSplit(%x):
?
  goto l1, l2, l3;
  label l1; call %y := p1(%x); goto done;
  label l2; call %y := p2(%x); goto done;
  label l3; call %y := p3(%x); goto done;
  label done;

// Should infer the same as for p123.
procedure (%y) := OneAngelicSplit(%x):
?
  call %y := p123(%x);

procedure (%y) := p1(%x): { %x = 1 || %x = 4 }(){ %y = 5 }
procedure (%y) := p2(%x): { %x = 2 || %x = 4 }(){ %y = 5 }
procedure (%y) := p3(%x): { %x = 3 || %x = 4 }(){ %y = 6 }
procedure (%y) := p123(%x):
  { %x = 1 || %x = 4 } () { %y = 5 }
  { %x = 2 || %x = 4 } () { %y = 5 }
  { %x = 3 || %x = 4 } () { %y = 6 }
