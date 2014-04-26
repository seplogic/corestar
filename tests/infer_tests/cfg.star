procedure Test1:
{emp}{emp} ?
nop;
label loop;
goto loop;
end;

// TODO: Should fail well-formedness checks.
procedure havoc(%y) {}(%y){}

procedure Test2:
{emp}{emp} ?
nop;
spec {%x=_x}(%x){@x=_x+1};
spec {%x=_x}(%x){@x=_x+1} + {x=_x}(){y>_x};
spec {%a=_x}(){@r=_x+1} [x/%a, y/%b] returns [y/@r];
spec {%a=_x}(){@r=_x+1} + {}(){} [x/@a] returns [y/@r];

spec {}(%x){};
call havoc(%x);

assign %x := {emp} () {/%x/emp} [%z] (%y);
label loop;
call %x := f((%x+%y), %y);
goto loop, and;
label and;
end;

procedure (%c) := f(%a,%b):

