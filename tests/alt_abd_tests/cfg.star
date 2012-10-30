Specification Test1:
{Emp}{Emp} ?
nop;
label loop;
goto loop;
end;

Specification Test2:
{Emp}{Emp} ?
nop;
assign x := {Emp}{Emp} (y);
label loop;
call x := f((x+y), y);
goto loop, and;
label and;
end;

Specification f:

