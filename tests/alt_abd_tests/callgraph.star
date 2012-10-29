Specification A: ?
call B();
call C();
end;

Specification B: ?
call C();
call D();
end;

Specification C: ?
call B();
call G();
end;

Specification D: ?
call E();
end;

Specification E: ?
call D();
call F();
end;

Specification F: ?
call B();
end;

Specification G: ?
call G();
call H();
end;

Specification H: ?
end;
