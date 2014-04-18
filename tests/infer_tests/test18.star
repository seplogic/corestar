// Tests for instantiating logical variables.

procedure Test18a:
  { @x = _x } (@x) { @x != _x }
?
  assign { @x = _y } (@x) { @x != _y } ();
end;

