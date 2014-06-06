procedure emit_$$(%x)
:
  call enqueue_$$(%x);
  call step_$$();
  spec {((@state!="error"))}(){((@state!="error"))};
procedure step_$$ 
  {((@state="error") * (@q0_0=_q0_0) * (@qsz="1"))}
  (@qsz)
  {((@state="error") * (@qsz="0"))}
  +
  {(((@q0_0=_q0_0) * (@q0_0!="returnIt") * (@qsz="1") * (@state="start")
      * (@q0_0!="callIt") * (@q0_0="callIt"))
    || ((@q0_0=_q0_0) * (@q0_0!="returnIt") * (@qsz="1") * (@state="start")
         * (@q0_0="returnIt") * (@q0_0!="callIt")))}
  (@qsz,@state,@qsz)
  {((@state="error") * (@qsz="0"))}
  +
  {(((@q0_0="callIt") * (@q0_0=_q0_0) * (@state="start") * (@qsz="1"))
    || ((@q0_0 ="returnIt") * (@q0_0=_q0_0) * (@q0_0="callIt")
         * (@state="start") * (@qsz="1"))
     || ((@q0_0="returnIt") * (@q0_0=_q0_0) * (@state="start")
         * (@qsz="1")))}
  (@qsz,@qsz,@qsz,@state,@qsz)
  {(((@state="start") * (@qsz="0")) || ((@state="error") * (@qsz="0")))}
  +
  {(((@q0_0=_q0_0) * (@q0_0!="returnIt") * (@qsz="1") * (@state="start")
      * (@q0_0!="callIt") * (@q0_0="callIt"))
    || ((@q0_0=_q0_0) * (@q0_0!="returnIt") * (@qsz="1") * (@state="start")
         * (@q0_0!="callIt") * (@q0_0="returnIt")))}
  (@qsz,@qsz)
  {((@state="start") * (@qsz="0"))}
  +
  {((@q0_0!="callIt") * (@q0_0!="returnIt") * (@q0_0=_q0_0)
     * (@state="start") * (@qsz="1"))}
  (@qsz)
  {((@state="start") * (@qsz="0"))}
procedure enqueue_$$(%x) 
  {(@qsz="0")}
  (@qsz,@q0_0)
  {((@q0_0=%x) * (@qsz="1"))}
