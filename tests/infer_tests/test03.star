

procedure (%y) := f(%x):
?
assign %y := {}{/%z/field(%z,"next",%x)} ();
end;

procedure Test04:
?
call %temp:=f(%y);
label a;
  call %temp:=f(%temp);
goto a;  // how do we specify conditional jumps?
end;



