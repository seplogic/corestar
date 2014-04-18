global @x;

procedure Test01:
?
assign {field(@x,"next",_x)}{field(@x,"next",nil())} (); // [@x]=NULL;
assign {field(@x,"next",_x)}{} (); // free(@x)
end;

// ====================

procedure Test02:
?
assign @x := {}{/%z/field(%z,"next","0")} (); // x=malloc()
// XXX assign x := {field(x,"next",_x)}{field($ret_v0,"next","0")} (); // [x]=0
end;

// ====================


procedure f(%x,%y):
?
assign {field(%x,"next",_x)}{field(%x,"next",%y)} ();
end;

procedure Test03:
?
call f(@x,"1");
call f(@x,"37");
end;

