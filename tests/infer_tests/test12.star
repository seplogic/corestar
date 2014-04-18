procedure Test12:
?
  call step();
end;

procedure step:
  { @state = "a" } (@state) { @state = "b" }
  { @state = "b" } (@state) { @state = "c" }
