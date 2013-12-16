procedure a:
  { $gs=1 * $gr1=_r1 * $gr2=_r2 * $gv1=_v1 * $gv2=_v2
    * _r1 = _v1 }
  ($gs,$gr1,$gr2,$gv1,$gv2)
  { $gs=2 * $gr1=_r1 * ($gr2=_v2) * $gv1=_v1 * $gv2=_v2 }
procedure b:
  { $gs=2 } ($gs) { $gs=1 }

procedure seq_a: ? call a();
procedure seq_aa: ? call a(); call a(); // should infer 0 triples
procedure seq_aba: ? call a(); call b(); call a(); // same as seq_a
