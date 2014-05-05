// Test parameters substitution

procedure f(%y) returns (%x)
  {} () {%x = %y}
:
  spec {} () {%a = %b} [%b<-%y] returns [%a<-%x];
