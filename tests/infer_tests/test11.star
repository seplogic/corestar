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

procedure Test11a:
?
  call step_a();
  call check_a();
end;

procedure step_a:
  { $g_state = "a" } ($g_state) { $g_state = "b" }
  { $g_state = "b" } ($g_state) { $g_state = "c" }

procedure check_a:
  { $g_state != "c" } () { $g_state != "c" }

procedure Test11b:
?
  call step_b();
end;

procedure step_b:
  { $g_state = "b" } () { $g_state = "b" }
