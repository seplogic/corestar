procedure Test1:
{Emp}{Emp} ?
nop;
label loop;
goto loop;
end;

procedure Test2:
{Emp}{Emp} ?
nop;
assign x := {Emp}{Emp} (y);
label loop;
call x := f((x+y), y);
goto loop, and;
label and;
end;

procedure f:

