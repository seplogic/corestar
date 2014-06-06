procedure Test00
:
spec {field(@x,"next",_x)}{field(@x,"next",nil())}; // [@x]=NULL;
spec {field(@x,"next",_x)}{}; // free(@x)
end;

// ====================

procedure Test02
:
spec {}{field(%z,"next","0")} returns [%z<-@x]; // x=malloc()
// XXX assign x := {field(x,"next",_x)}{field($ret_v0,"next","0")} (); // [x]=0
end;

// ====================


procedure f(%x,%y)
:
spec {field(%x,"next",_x)}{field(%x,"next",%y)};
end;

procedure Test03
:
call f(@x,"1");
call f(@x,"37");
end;

