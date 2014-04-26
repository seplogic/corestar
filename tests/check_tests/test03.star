procedure test03
 { @par = _par } () { @pos = _par }
:
 spec
  { @par = _par1 * @par = _par2 * @par = _par3 }
  ()
  { @pos = _par1 * @pos = _par2 * @pos = _par3 };

procedure test03_a
  { @par = _par * _par = _pos } (@pos) { @par = _par * @pos = _pos }
:
  spec
    { @par = _par * %par = _pos1 * _par = _pos2 }
    (@pos)
    { @par = _par * @pos = _pos1 * @pos = _pos2 };

procedure test03_b
  { @par = _par * _par = _pos1 * _par = _pos2 }
  (@pos)
  { @par = _par * @pos = _pos1 * @pos = _pos2 }
:
  spec
    { @par = _par * _par = _pos }
    (@pos)
    { @par = _par * @pos = _pos };

procedure test03_c
  { @par = _par1 * @par = _par2 * @par = _par3 }
  ()
  { @pos = _par1 * @pos = _par2 * @pos = _par3 }
:
  spec { @par = _par } () { @pos = _par };

procedure test03_d
  { @par = _par1 * _par1 = _pos1 } () { @pos = _par1 }
:
  spec { @par = _par * _par = _pos } () { @pos = _par };

procedure test03_e
  { @par != _par1 * _par1 = _pos1 } () { @pos = _par1 }
:
  spec { @par != _par * _par = _pos } () { @pos = _par };

