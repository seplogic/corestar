

procedure f:
?
assign $ret_v0 := {}{field($ret_v0,"next",@parameter0:)} ();
end;

procedure Test04:
?
call temp:=f(y);
label a;
  call temp:=f(temp);
goto a;  // how do we specify conditional jumps?
end;




