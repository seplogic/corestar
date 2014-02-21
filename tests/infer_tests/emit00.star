procedure emit_$$(x):
  
?
  call :=enqueue_$$(x);
  call :=step_$$();
  assign :={(($gstate!="error"))}(){(($gstate!="error"))}[]();
procedure step_$$ :
  {(($gstate="error") * ($gq0_0=_q0_0) * ($gqsz="1"))}
  ($gqsz)
  {(($gstate="error") * ($gqsz="0"))}
  +
  {((($gq0_0=_q0_0) * ($gq0_0!="returnIt") * ($gqsz="1") * ($gstate="start")
      * ($gq0_0!="callIt") * ($gq0_0="callIt"))
    || (($gq0_0=_q0_0) * ($gq0_0!="returnIt") * ($gqsz="1") * ($gstate="start")
         * ($gq0_0="returnIt") * ($gq0_0!="callIt")))}
  ($gqsz,$gstate,$gqsz)
  {(($gstate="error") * ($gqsz="0"))}
  +
  {((($gq0_0="callIt") * ($gq0_0=_q0_0) * ($gstate="start") * ($gqsz="1"))
    || (($gq0_0 ="returnIt") * ($gq0_0=_q0_0) * ($gq0_0="callIt")
         * ($gstate="start") * ($gqsz="1"))
     || (($gq0_0="returnIt") * ($gq0_0=_q0_0) * ($gstate="start")
         * ($gqsz="1")))}
  ($gqsz,$gqsz,$gqsz,$gstate,$gqsz)
  {((($gstate="start") * ($gqsz="0")) || (($gstate="error") * ($gqsz="0")))}
  +
  {((($gq0_0=_q0_0) * ($gq0_0!="returnIt") * ($gqsz="1") * ($gstate="start")
      * ($gq0_0!="callIt") * ($gq0_0="callIt"))
    || (($gq0_0=_q0_0) * ($gq0_0!="returnIt") * ($gqsz="1") * ($gstate="start")
         * ($gq0_0!="callIt") * ($gq0_0="returnIt")))}
  ($gqsz,$gqsz)
  {(($gstate="start") * ($gqsz="0"))}
  +
  {(($gq0_0!="callIt") * ($gq0_0!="returnIt") * ($gq0_0=_q0_0)
     * ($gstate="start") * ($gqsz="1"))}
  ($gqsz)
  {(($gstate="start") * ($gqsz="0"))}
procedure enqueue_$$(x) :
  {($gqsz="0")}
  ($gqsz,$gq0_0)
  {(($gq0_0=x) * ($gqsz="1"))} [x]
