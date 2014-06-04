procedure A:
call B();
call C();
end;

procedure B:
call C();
call D();
end;

procedure C:
call B();
call G();
end;

procedure D:
call E();
end;

procedure E:
call D();
call F();
end;

procedure F:
call B();
end;

procedure G:
call G();
call H();
end;

procedure H:
end;
