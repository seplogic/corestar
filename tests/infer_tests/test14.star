procedure Test14
:
  call step();
end;

procedure step
  { @state = "a" } (@state) { @state = "b" || @state = "c" }
