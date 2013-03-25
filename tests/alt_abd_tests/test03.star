

Specification f:
?
assign  := {}{$ret_v1=@parameter1: * field(@parameter0:,"next",@parameter1:)} ();
end;

Specification Test04:
?
call temp:=f(y);
label a;
  call temp:=f(temp);
goto a;  // how do we specify conditional jumps?
end;




