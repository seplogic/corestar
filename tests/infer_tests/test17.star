procedure Test17:
?
  call step();
  call check();
end;

procedure step:
  { $g_state = "a" } ($g_state) { $g_state = "b" }

procedure check:
  { $g_queue_size = "1" } () { $g_state = "b" }
