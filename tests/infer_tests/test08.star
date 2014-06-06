rule remove_foo:
  foo(?v) * ?f |- foo(?w) * ?g
if
  foo(?v) * ?f |- foo(?v) * ?v = ?w * ?g
;

procedure Test08 {foo(bar(twelve()))}{foo(bar(_x))}
:
end;
