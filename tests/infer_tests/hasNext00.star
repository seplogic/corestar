procedure emit_$$ (x, y):
?
  call :=enqueue_$$(x,y);
  call :=step_$$();
  assign :={(($g_state!="HasNexterror"))}(){(($g_state!="HasNexterror"))}();

procedure step_$$ :
  // loop/skip on "start"
  {(($g_qsz="2")
    *($g_q_1_1=_q_1_1)
    *($g_rI=_rI_0)
    *($g_q_1_0=_q_1_0)
    *($g_state="HasNextstart")
    *($g_q_0_1=_q_0_1)
    *($g_q_0_0=_q_0_0))
   }
  ($g_qsz,$g_q_0_1
  ,$g_q_0_0)
  {(($g_state="HasNextstart")
   *($g_rI=_rI_0)
   *($g_q_0_1=_q_1_1)
   *($g_q_0_0=_q_1_0)
   *($g_qsz="1"))
  }
  // skip on "invalid"
  +{((($g_rI=_rI_0)*($g_qsz="2")
     *($g_q_0_0=_q_0_0)
     *($g_q_0_1=_q_0_1)
     *($g_q_1_0=_q_1_0)
     *($g_q_1_1=_q_1_1)
     *($g_state="HasNextinvalid")
     *(_rI_1_1=_rI_0))
    ||(($g_q_0_0=_q_0_0)
      *($g_q_1_1=0)
      *($g_q_0_1=_q_0_1)
      *($g_rI=_rI_0)
      *($g_state="HasNextinvalid")
      *($g_q_1_0=_q_1_0)
      *($g_qsz="2")
      *($g_q_1_1=_q_1_1)
      *(_rI_1_1=_rI_0))
    ||(($g_q_0_1!=_rI_0)
      *($g_q_0_0=_q_0_0)
      *($g_q_0_1=_q_0_1)
      *($g_rI=_rI_0)
      *($g_state="HasNextinvalid")
      *($g_q_1_0=_q_1_0)
      *($g_q_1_1=_q_1_1)
      *($g_qsz="2")
      *(_rI_1_1=_rI_0))
    ||(($g_rI=_rI_0)
      *($g_state="HasNextinvalid")
      *($g_q_0_1!=_rI_0)
      *($g_q_1_1=0)
      *($g_q_1_1=_q_1_1)
      *($g_q_0_1=_q_0_1)
      *($g_qsz="2")
      *($g_q_1_0=_q_1_0)
      *($g_q_0_0=_q_0_0)
      *(_rI_1_1=_rI_0))
    ||(($g_qsz="2")
      *($g_q_1_1=_q_1_1)
      *($g_rI=_rI_0)
      *($g_q_1_0=_q_1_0)
      *($g_state="HasNextinvalid")
      *($g_q_0_1=_q_0_1)
      *($g_q_0_0=_q_0_0))
    ||(($g_rI=_rI_0)*($g_qsz="2")
      *($g_q_0_1=_q_0_1)
      *($g_q_0_0=_q_0_0)
      *($g_q_1_1=_q_1_1)
      *($g_q_1_0=_q_1_0)
      *($g_q_0_1!=_rI_0)
      *($g_state="HasNextinvalid"))
    ||(($g_rI=_rI_0)*($g_qsz="2")
      *($g_q_0_0=_q_0_0)
      *($g_q_0_1=_q_0_1)
      *($g_q_0_1!=_rI_0)
      *($g_q_1_0=_q_1_0)
      *($g_q_1_1=_q_1_1)
      *($g_state="HasNextinvalid"))
    )
   }
  ($g_qsz,$g_q_0_1
  ,$g_q_0_0)
  {(($g_rI=_rI_0)
   *($g_q_0_1=_q_1_1)
   *($g_state="HasNextinvalid")
   *($g_q_0_0=_q_1_0)
   *($g_qsz="1"))
  }
  // skip on "valid"
  +{((($g_rI=_rI_0)*($g_qsz="2")
     *($g_q_0_1=_q_0_1)
     *($g_q_0_0=_q_0_0)
     *($g_state="HasNextvalid")
     *($g_q_1_1=_q_1_1)
     *($g_q_1_0=_q_1_0)
     *($g_q_0_1!=_rI_0))
    ||(($g_qsz="2")
      *($g_q_1_1=_q_1_1)
      *($g_rI=_rI_0)
      *($g_q_1_0=_q_1_0)
      *($g_q_0_1=_q_0_1)
      *($g_state="HasNextvalid")
      *($g_q_0_0=_q_0_0))
    )
   }
  ($g_qsz,$g_q_0_1
  ,$g_q_0_0)
  {(($g_rI=_rI_0)
   *($g_q_0_1=_q_1_1)
   *($g_q_0_0=_q_1_0)
   *($g_state="HasNextvalid")
   *($g_qsz="1"))
  }
  // skip on "error"
  +{(($g_qsz="2")
    *($g_state="HasNexterror")
    *($g_q_1_1=_q_1_1)
    *($g_rI=_rI_0)
    *($g_q_1_0=_q_1_0)
    *($g_q_0_1=_q_0_1)
    *($g_q_0_0=_q_0_0))
   }
  ($g_qsz,$g_q_0_1
  ,$g_q_0_0)
  {(($g_rI=_rI_0)
   *($g_q_0_1=_q_1_1)
   *($g_q_0_0=_q_1_0)
   *($g_state="HasNexterror")
   *($g_qsz="1"))
  }

procedure enqueue_$$(x,y) :
  {($g_qsz="0")}
  ($g_qsz,$g_q_0_0
  ,$g_q_0_1)
  {(($g_qsz="1")
   *($g_q_0_0=x)
   *($g_q_0_1=y))
  }[x,y]+{($g_qsz="1")}
  ($g_qsz,$g_q_1_0
  ,$g_q_1_1)
  {(($g_qsz="2")
   *($g_q_1_0=x)
   *($g_q_1_1=y))
  }[x,y]


procedure HasNext.print$$java.util.Iterator$$void(x) :
?
  call 
    :=emit_$$("call_$$_HasNext.print$$java.util.Iterator$$void"
             ,x);
  call :=HasNext.print$$java.util.Iterator$$void_I(x);
  call :=emit_$$("return_$$_HasNext.print$$java.util.Iterator$$void");
procedure HasNext.print$$java.util.Iterator$$void_I(x) :
  
?
  assign r0:={()}(){/a/(a=x)}();
  call $temp:=java.util.Iterator.hasNext$$$$boolean();
  assign $z0:={()}(){/a/(a=$temp)}();
  goto gen_1,gen_2;
  label gen_1;
  assign :={()}(){($z0=0)}();
  goto label0;
  label gen_2;
  assign :={()}(){($z0!=0)}();
  call :=java.util.Iterator.next$$$$java.lang.Object();
  label label0;
  nop;
procedure (b) := java.util.Iterator.hasNext$$$$boolean :
  
?
  call :=emit_$$("call_$$_java.util.Iterator.hasNext$$$$boolean");
  call b:=java.util.Iterator.hasNext$$$$boolean_I();
  call :=emit_$$("return_$$_java.util.Iterator.hasNext$$$$boolean");
procedure (b) := java.util.Iterator.hasNext$$$$boolean_I :
  {}(){}
procedure java.util.Iterator.next$$$$java.lang.Object :
  
?
  call :=emit_$$("call_$$_java.util.Iterator.next$$$$java.lang.Object");
  call z:=java.util.Iterator.next$$$$java.lang.Object_I();
  call 
    :=emit_$$("return_$$_java.util.Iterator.next$$$$java.lang.Object");
procedure (a) := java.util.Iterator.next$$$$java.lang.Object_I :

