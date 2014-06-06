// Test that inferred specs take into account return arguments

procedure f(%y) returns (%x)
:
spec {}(){%w = %y} returns [%w<-%x];
