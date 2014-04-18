procedure Test17:
?
  call step();
  call check();
end;

procedure step:
  { @state = "a" } (@state) { @state = "b" }

procedure check:
  { @queue_size = "1" } () { }
