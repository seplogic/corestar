global @state;

procedure test01_a:
  { @state = "foo" || @state = "bar" }
  { @state != "foobar" }
?
end;

procedure test01_b:
  { @state = "foo" }
  { @state != "foobar" }
?
end;
