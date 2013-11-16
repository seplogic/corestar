global state;

procedure enqueue:
  { $g_size = "0" }
  ($g_size, $g_loc_0)
  { $g_size = "1" * $g_loc_0 = @parameter0: }

  { $g_size = "1" * $g_loc_0 = _e }
  ($g_size, $g_loc_0, $g_loc_1)
  { $g_size = "2" * $g_loc_0 = @parameter0: * $g_loc_1 = _e }

procedure step:
  { $g_size = "1" * $g_loc_0 != "1" * $g_state = "Start" }
  ($g_size, $g_state)
  { $g_size = "0" * $g_state = "Start" }

  { $g_size = "1" * $g_loc_0 = "1" * $g_state = "Start" }
  ($g_size, $g_state)
  { $g_size = "0" * $g_state = "Error" }

procedure emit:
?
  call enqueue(@parameter0:);
  call step();
  assign { $g_state != "Error" }{ $g_state != "Error" } ();
end;

procedure init:
?
  assign {}($g_size){ $g_size = "0" } ();
  assign {}($g_state){ $g_state = "Start" } ();
end;

procedure Test19:
?
  call init();
  call emit("3");
end;
