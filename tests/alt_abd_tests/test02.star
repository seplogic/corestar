

Specification f:
?
assign  := {field(@parameter0:,"next",_x)}{field(@parameter0:,"next",@parameter1:)} ();
end;

Specification Test04:
?
call f(y,"0");
call f(x,"y");
call f(z,"z");
call f(w,"w");
assign y := {}{$ret_v1="0"} (); // y=NULL
assign x := {}{$ret_v1="0"} (); // x=NULL
assign z := {}{$ret_v1="0"} (); // z=NULL
end;




