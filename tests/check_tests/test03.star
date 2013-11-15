global state;

procedure test03:
 { $g_par = _par } () { $g_pos = _par }
?
 assign { $g_par = _par1 * $g_par = _par2 * $g_par = _par3 } ()
        { $g_pos = _par1 * $g_pos = _par2 * $g_pos = _par3 } ();
end;

procedure test03_a:
 { $g_par = _par * _par = _pos } ($g_pos) { $g_par = _par * $g_pos = _pos }
?
 assign { $g_par = _par * par = _pos1 * _par = _pos2 } ($g_pos)
        { $g_par = _par * $g_pos = _pos1 * $g_pos = _pos2 } ();
end;

procedure test03_b:
 { $g_par = _par * _par = _pos1 * _par = _pos2 } ($g_pos)
 { $g_par = _par * $g_pos = _pos1 * $g_pos = _pos2 }
?
 assign { $g_par = _par * _par = _pos } ($g_pos)
        { $g_par = _par * $g_pos = _pos } ();
end;

procedure test03_c:
 { $g_par = _par1 * $g_par = _par2 * $g_par = _par3 } ()
 { $g_pos = _par1 * $g_pos = _par2 * $g_pos = _par3 }
?
 assign { $g_par = _par } () { $g_pos = _par } ();
end;

procedure test03_d:
 { $g_par = _par1 * _par1 = _pos1 } () { $g_pos = _par1 }
?
 assign { $g_par = _par * _par = _pos } () { $g_pos = _par } ();
end;

procedure test03_e:
 { $g_par != _par1 * _par1 = _pos1 } () { $g_pos = _par1 }
?
 assign { $g_par != _par * _par = _pos } () { $g_pos = _par } ();
end;
