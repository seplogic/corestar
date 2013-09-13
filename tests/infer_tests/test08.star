rule remove_foo:
 | foo(?v) |- foo(?w)
if
  foo(?v) | |- ?v = ?w

procedure Test08: {foo(bar(twelve()))}{foo(bar(_x))}
?
end;
