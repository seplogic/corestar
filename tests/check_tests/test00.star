globals x, y, z;

procedure a:
  {ls(x,_y) * ls(_y,nil())}
  {ls(x,nil())}
?
end;

procedure b:
  {ls(z,_y) * ls(x,_y) * ls(_y,nil())}
  {ls(x,nil()) * ls(z,_y)}
!
end;
