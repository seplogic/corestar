procedure Test11:
?
  call step();
  call check();
end;

procedure step:
  { @state = "a" } { @state = "b" }
  { @state = "b" } { @state = "c" }

procedure check:
  { @state != "c" } { @state != "c" }

procedure Test11a:
?
  call step_a();
  call check_a();
end;

procedure step_a:
  { @state = "a" } (@state) { @state = "b" }
  { @state = "b" } (@state) { @state = "c" }

procedure check_a:
  { @state != "c" } () { @state != "c" }

procedure Test11b:
?
  call step_b();
end;

procedure step_b:
  { @state = "b" } () { @state = "b" }
