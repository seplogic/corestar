procedure enqueue(%x)
  { @size = "0" }
  (@size, @loc_0)
  { @size = "1" * @loc_0 = %x }
+
  { @size = "1" * @loc_0 = _e }
  (@size, @loc_0, @loc_1)
  { @size = "2" * @loc_0 = %x * @loc_1 = _e }

procedure step
  { @size = "1" * @loc_0 != "1" * @state = "Start" }
  (@size, @state)
  { @size = "0" * @state = "Start" }
+
  { @size = "1" * @loc_0 = "1" * @state = "Start" }
  (@size, @state)
  { @size = "0" * @state = "Error" }

procedure emit(%x):
  call enqueue(%x);
  call step();
  spec { @state != "Error" }{ @state != "Error" };
end;

procedure init:
  spec {}(@size){ @size = "0" };
  spec {}(@state){ @state = "Start" };
end;

procedure Test19:
  call init();
  call emit("3");
end;
