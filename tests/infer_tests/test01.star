procedure Test01:
?
assign  := {field(x,"next",_x)}{field(x,"next",NULL)} (); // [x]=NULL;
assign  := {field(x,"next",_x)}{} (); // free(x)
end;

// ====================

procedure Test02:
? 
assign x := {}{field($ret_v1,"next",_x)} (); // x=malloc()
assign x := {field($ret_v1,"next","0")}{} (); // [x]=0
end;

// ====================


procedure f:
?
assign  := {field(@parameter0:,"next",_x)}{field(@parameter0:,"next",@parameter1:)} ();
end;

procedure Test03:
?
call f(y,"1");
call f(y,"37");
end;




