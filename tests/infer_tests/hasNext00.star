procedure emit_$$ (%x, %y)
:
  call enqueue_$$(%x,%y);
  call step_$$();
  spec {((@state!="HasNexterror"))}(){((@state!="HasNexterror"))};

procedure step_$$ 
  // loop/skip on "start"
  {((@qsz="2")
    *(@q_1_1=_q_1_1)
    *(@rI=_rI_0)
    *(@q_1_0=_q_1_0)
    *(@state="HasNextstart")
    *(@q_0_1=_q_0_1)
    *(@q_0_0=_q_0_0))
   }
  (@qsz,@q_0_1
  ,@q_0_0)
  {((@state="HasNextstart")
   *(@rI=_rI_0)
   *(@q_0_1=_q_1_1)
   *(@q_0_0=_q_1_0)
   *(@qsz="1"))
  }
  // skip on "invalid"
  +{(((@rI=_rI_0)*(@qsz="2")
     *(@q_0_0=_q_0_0)
     *(@q_0_1=_q_0_1)
     *(@q_1_0=_q_1_0)
     *(@q_1_1=_q_1_1)
     *(@state="HasNextinvalid")
     *(_rI_1_1=_rI_0))
    ||((@q_0_0=_q_0_0)
      *(@q_1_1=0)
      *(@q_0_1=_q_0_1)
      *(@rI=_rI_0)
      *(@state="HasNextinvalid")
      *(@q_1_0=_q_1_0)
      *(@qsz="2")
      *(@q_1_1=_q_1_1)
      *(_rI_1_1=_rI_0))
    ||((@q_0_1!=_rI_0)
      *(@q_0_0=_q_0_0)
      *(@q_0_1=_q_0_1)
      *(@rI=_rI_0)
      *(@state="HasNextinvalid")
      *(@q_1_0=_q_1_0)
      *(@q_1_1=_q_1_1)
      *(@qsz="2")
      *(_rI_1_1=_rI_0))
    ||((@rI=_rI_0)
      *(@state="HasNextinvalid")
      *(@q_0_1!=_rI_0)
      *(@q_1_1=0)
      *(@q_1_1=_q_1_1)
      *(@q_0_1=_q_0_1)
      *(@qsz="2")
      *(@q_1_0=_q_1_0)
      *(@q_0_0=_q_0_0)
      *(_rI_1_1=_rI_0))
    ||((@qsz="2")
      *(@q_1_1=_q_1_1)
      *(@rI=_rI_0)
      *(@q_1_0=_q_1_0)
      *(@state="HasNextinvalid")
      *(@q_0_1=_q_0_1)
      *(@q_0_0=_q_0_0))
    ||((@rI=_rI_0)*(@qsz="2")
      *(@q_0_1=_q_0_1)
      *(@q_0_0=_q_0_0)
      *(@q_1_1=_q_1_1)
      *(@q_1_0=_q_1_0)
      *(@q_0_1!=_rI_0)
      *(@state="HasNextinvalid"))
    ||((@rI=_rI_0)*(@qsz="2")
      *(@q_0_0=_q_0_0)
      *(@q_0_1=_q_0_1)
      *(@q_0_1!=_rI_0)
      *(@q_1_0=_q_1_0)
      *(@q_1_1=_q_1_1)
      *(@state="HasNextinvalid"))
    )
   }
  (@qsz,@q_0_1
  ,@q_0_0)
  {((@rI=_rI_0)
   *(@q_0_1=_q_1_1)
   *(@state="HasNextinvalid")
   *(@q_0_0=_q_1_0)
   *(@qsz="1"))
  }
  // skip on "valid"
  +{(((@rI=_rI_0)*(@qsz="2")
     *(@q_0_1=_q_0_1)
     *(@q_0_0=_q_0_0)
     *(@state="HasNextvalid")
     *(@q_1_1=_q_1_1)
     *(@q_1_0=_q_1_0)
     *(@q_0_1!=_rI_0))
    ||((@qsz="2")
      *(@q_1_1=_q_1_1)
      *(@rI=_rI_0)
      *(@q_1_0=_q_1_0)
      *(@q_0_1=_q_0_1)
      *(@state="HasNextvalid")
      *(@q_0_0=_q_0_0))
    )
   }
  (@qsz,@q_0_1
  ,@q_0_0)
  {((@rI=_rI_0)
   *(@q_0_1=_q_1_1)
   *(@q_0_0=_q_1_0)
   *(@state="HasNextvalid")
   *(@qsz="1"))
  }
  // skip on "error"
  +{((@qsz="2")
    *(@state="HasNexterror")
    *(@q_1_1=_q_1_1)
    *(@rI=_rI_0)
    *(@q_1_0=_q_1_0)
    *(@q_0_1=_q_0_1)
    *(@q_0_0=_q_0_0))
   }
  (@qsz,@q_0_1
  ,@q_0_0)
  {((@rI=_rI_0)
   *(@q_0_1=_q_1_1)
   *(@q_0_0=_q_1_0)
   *(@state="HasNexterror")
   *(@qsz="1"))
  }

procedure enqueue_$$(%x,%y) 
  {(@qsz="0")}
  (@qsz,@q_0_0
  ,@q_0_1)
  {((@qsz="1")
   *(@q_0_0=%x)
   *(@q_0_1=%y))
  }[%x,%y]+{(@qsz="1")}
  (@qsz,@q_1_0
  ,@q_1_1)
  {((@qsz="2")
   *(@q_1_0=%x)
   *(@q_1_1=%y))
  }


procedure HasNext.print$$java.util.Iterator$$void(%x) 
:
  call 
    :=emit_$$("call_$$_HasNext.print$$java.util.Iterator$$void"
             ,%x);
  call HasNext.print$$java.util.Iterator$$void_I(%x);
  call emit_$$("return_$$_HasNext.print$$java.util.Iterator$$void");
procedure HasNext.print$$java.util.Iterator$$void_I(%x) 
  
:
  spec {()}(){%a=%x} returns [%a<-%r0];
  call %temp:=java.util.Iterator.hasNext$$$$boolean();
  spec {()}(){%a=%temp} returns [%a<-%z0];
  goto gen_1,gen_2;
  label gen_1;
  spec {()}(){(%z0=0)};
  goto label0;
  label gen_2;
  spec {()}(){(%z0!=0)};
  call java.util.Iterator.next$$$$java.lang.Object();
  label label0;
  nop;
procedure java.util.Iterator.hasNext$$$$boolean returns (%b)
  
:
  call emit_$$("call_$$_java.util.Iterator.hasNext$$$$boolean");
  call %b:=java.util.Iterator.hasNext$$$$boolean_I();
  call emit_$$("return_$$_java.util.Iterator.hasNext$$$$boolean");
procedure (%b) := java.util.Iterator.hasNext$$$$boolean_I 
  {}(){}
procedure java.util.Iterator.next$$$$java.lang.Object 
  
:
  call emit_$$("call_$$_java.util.Iterator.next$$$$java.lang.Object");
  call %z:=java.util.Iterator.next$$$$java.lang.Object_I();
  call 
    :=emit_$$("return_$$_java.util.Iterator.next$$$$java.lang.Object");
procedure java.util.Iterator.next$$$$java.lang.Object_I returns (%a)

