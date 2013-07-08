procedure Test11:
?
  call step();
  call check();
end;

procedure step:
  { $g_state = "a" } { $g_state = "b" }
  { $g_state = "b" } { $g_state = "c" }

procedure check:
  { $g_state != "c" } { $g_state != "c" }
