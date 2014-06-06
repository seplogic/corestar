procedure f(%x) returns (%y)
:
spec {}{field(%z,"next",%x)} returns [%z<-%y];
end;

procedure Test04
:
call %temp:=f(%y);
label a;
  call %temp:=f(%temp);
goto a;  // how do we specify conditional jumps:
end;



