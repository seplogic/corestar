procedure Test15
:
  call step();
  call step();
end;

procedure step
  { @state = "a" } (@state) { @state = "b" }
  { @state = "b" } (@state) { @state = "c" }
