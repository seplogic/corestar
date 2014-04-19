// Test parameters substitution

procedure (%x) := f(%y): {}{/%w/%w = %z} [%z]
?
assign %x := {}(){/%a/ %a = %b} [%b] (%y);
