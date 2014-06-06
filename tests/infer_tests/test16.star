procedure Test16:
  call step();
  call step();
end;

procedure step
  { @state = "a" } { @state = "b" }
  { @state = "b" } { @state = "c" }
