global x;

procedure Test01:
?
assign {field($g_x,"next",_x)}{field($g_x,"next",nil())} (); // [x]=NULL;
assign {field($g_x,"next",_x)}{} (); // free(x)
end;

// ====================

procedure Test02:
?
assign $g_x := {}{field($ret_v0,"next","0")} (); // x=malloc()
// XXX assign x := {field(x,"next",_x)}{field($ret_v0,"next","0")} (); // [x]=0
end;

// ====================


procedure f:
?
assign {field(@parameter0:,"next",_x)}{field(@parameter0:,"next",@parameter1:)} ();
end;

procedure Test03:
?
call f(y,"1");
call f(y,"37");
end;

