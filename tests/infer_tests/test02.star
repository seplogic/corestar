

procedure f(%x,%y)
:
spec {field(%x,"next",_x)}{field(%x,"next",%y)};
end;

procedure Test04
:
call f(%y,0);
call f(%x,"x");
call f(%z,"z");
call f(%w,"w");
spec {}{%a=0} returns [%a<-%y]; // y=NULL
spec {}{%a=0} returns [%a<-%x]; // x=NULL
spec {}{%a=0} returns [%a<-%z]; // z=NULL
end;




