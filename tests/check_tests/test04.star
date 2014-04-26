procedure test04
  { @state = "foobar" }
  { @state = "foo" || @state != "bar" }
: end;

procedure test04_a
  { (@state = "foo" || @state = "bar") * (@next_state = "foo" || @next_state = "bar") * (@next_state != @state) }
  { (@state = "foo" * @next_state = "bar") || (@state = "bar" * @next_state = "foo") }
: end;

procedure test04_b
  { (@state = "foo" * @size = "1") || (@state = "bar" * @size = "2") }
  { (@state = "foo" || @state = "bar") * (@size = "1" || @size = "2") }
: end;
