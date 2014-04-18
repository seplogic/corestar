

procedure f(%x,%y):
?
assign  := {field(%x,"next",_x)}{field(%x,"next",%y)} ();
end;

procedure Test04:
?
call f(%y,0);
call f(%x,"x");
call f(%z,"z");
call f(%w,"w");
assign %y := {}{/%a/%a=0} (); // y=NULL
assign %x := {}{/%a/%a=0} (); // x=NULL
assign %z := {}{/%a/%a=0} (); // z=NULL
end;




