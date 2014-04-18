procedure a:
  { @x = _x } () { _x < 0 || _x >= 0 }
procedure b:
  { @x = _y } () { _y < 0 || _y >= 0 }
? call a();
