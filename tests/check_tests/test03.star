global @state;

procedure test03:
 { @par = _par } () { @pos = _par }
?
 assign { @par = _par1 * @par = _par2 * @par = _par3 } ()
        { @pos = _par1 * @pos = _par2 * @pos = _par3 } ();
end;

procedure test03_a:
 { @par = _par * _par = _pos } (@pos) { @par = _par * @pos = _pos }
?
 assign { @par = _par * %par = _pos1 * _par = _pos2 } (@pos)
        { @par = _par * @pos = _pos1 * @pos = _pos2 } ();
end;

procedure test03_b:
 { @par = _par * _par = _pos1 * _par = _pos2 } (@pos)
 { @par = _par * @pos = _pos1 * @pos = _pos2 }
?
 assign { @par = _par * _par = _pos } (@pos)
        { @par = _par * @pos = _pos } ();
end;

procedure test03_c:
 { @par = _par1 * @par = _par2 * @par = _par3 } ()
 { @pos = _par1 * @pos = _par2 * @pos = _par3 }
?
 assign { @par = _par } () { @pos = _par } ();
end;

procedure test03_d:
 { @par = _par1 * _par1 = _pos1 } () { @pos = _par1 }
?
 assign { @par = _par * _par = _pos } () { @pos = _par } ();
end;

procedure test03_e:
 { @par != _par1 * _par1 = _pos1 } () { @pos = _par1 }
?
 assign { @par != _par * _par = _pos } () { @pos = _par } ();
end;
