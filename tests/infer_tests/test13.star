procedure Test13
:
  call step();
end;

procedure step
  { @state = "a" } (@state) { @state = "b" }
