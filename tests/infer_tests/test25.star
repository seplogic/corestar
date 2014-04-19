// Test that inferred specs take into account return arguments

procedure (%x) := f(%y):
?
assign %x := {}(){/%w/ %w = %y} [] ();
