procedure Test15:
?
  call step();
  call step();
end;

procedure step:
  { $g_state = "a" } { $g_state = "b" }
  { $g_state = "b" } { $g_state = "c" }
