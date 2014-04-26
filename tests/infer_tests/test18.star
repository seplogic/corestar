// Tests for instantiating logical variables.

procedure Test18a
  { @x = _x } (@x) { @x != _x }
:
  spec { @x = _y } (@x) { @x != _y };
