procedure Test1:
  label loop;
  goto loop;

procedure havoc(%y)
  {}(%y){}

procedure Test2:
  spec {@x=_x}(@x){@x=_x+1};
  spec {@x=_x}(@x){@x=_x+1} + {@x=_x}(){@y>_x};
  spec {%a=_x}(){%r=_x+1} [%a,%b <- @x,@y] returns [%r<-@y];
  spec {%a=_x}(){%r=_x+1} + {}(){} [%a<-@x] returns [%r<-@y];

  spec {}(@x){};
  call havoc(@x);

  label loop;
  call @x := f(@x+@y, @y);
  goto loop, done;
  label done;

procedure f(%a,%b) returns (%c)


