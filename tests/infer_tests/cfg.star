procedure Test1:
{emp}{emp} ?
nop;
label loop;
goto loop;
end;

procedure Test2:
{emp}{emp} ?
nop;
assign x := {emp} () {/x/emp} [z] (y);
label loop;
call x := f((x+y), y);
goto loop, and;
label and;
end;

procedure (c) := f(a,b):

