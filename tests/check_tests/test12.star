procedure a:
  { $gx = _x } () { _x < 0 || _x >= 0 }
procedure b:
  { $gx = _y } () { _y < 0 || _y >= 0 }
? call a();
