procedure a:
  { @s=1 * @r1=_r1 * @r2=_r2 * @v1=_v1 * @v2=_v2
    * _r1 = _v1 }
  (@s,@r1,@r2,@v1,@v2)
  { @s=2 * @r1=_r1 * (@r2=_v2) * @v1=_v1 * @v2=_v2 }
procedure b:
  { @s=1 * @r1=_r1 * @r2=_r2 * @v1=_v1 * @v2=_v2
    * _r1 = _v1 }
  (@s,@r1,@r2,@v1,@v2)
  { @s=2 * @r1=_r1 * (@r2=_v2) * @v1=_v1 * @v2=_v2 }
? call a();
