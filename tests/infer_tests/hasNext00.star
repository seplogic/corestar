    procedure emit_$$ :
      
    ?
      call :=enqueue_$$(@parameter0:,@parameter1:);
      call :=step_$$();
      assign :={(($g_state!="HasNexterror"))}()
        {(($g_state!="HasNexterror"))}();
    procedure step_$$ :
      {()}
      ($g_qsz,$g_state,$g_rI
      ,$g_qsz)
      {(($g_rI=_rI_2_1)
       *($g_state="HasNextvalid")
       *($g_qsz="0"))
      }+{()}
      ($g_qsz,$g_state,$g_rI
      ,$g_qsz,$g_q_0_1
      ,$g_q_0_0)
      {(($g_q_0_1=_q_1_1)
       *($g_q_0_0=_q_1_0)
       *($g_state="HasNexterror")
       *($g_rI=_rI_1_0)
       *($g_qsz="1"))
      }+{()}
      ($g_qsz,$g_state,$g_rI
      ,$g_qsz,$g_qsz
      ,$g_state,$g_rI,$g_qsz
      ,$g_q_0_1,$g_q_0_0)
      {((($g_rI=_rI_2_1)
        *($g_state="HasNextvalid")
        *($g_qsz="0"))
       ||(($g_q_0_1=_q_1_1)
         *($g_q_0_0=_q_1_0)
         *($g_state="HasNexterror")
         *($g_rI=_rI_1_0)
         *($g_qsz="1"))
       )
      }+{()}
      ($g_qsz,$g_state,$g_rI
      ,$g_qsz,$g_q_0_1
      ,$g_q_0_0)
      {(($g_q_0_1=_q_1_1)
       *($g_state="HasNextinvalid")
       *($g_q_0_0=_q_1_0)
       *($g_rI=_rI_1_0)
       *($g_qsz="1"))
      }+{()}
      ($g_qsz,$g_rI,$g_qsz
      ,$g_q_0_1,$g_q_0_0
      ,$g_qsz,$g_state,$g_rI
      ,$g_qsz,$g_q_0_1
      ,$g_q_0_0)
      {((($g_state="HasNextstart")
        *($g_q_0_1=_q_1_1)
        *($g_q_0_0=_q_1_0)
        *($g_rI=_rI_1_1)
        *($g_qsz="1"))
       ||(($g_q_0_1=_q_1_1)
         *($g_state="HasNextinvalid")
         *($g_q_0_0=_q_1_0)
         *($g_rI=_rI_1_0)
         *($g_qsz="1"))
       )
      }
      +{(($g_qsz="2")
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
      +{((($g_rI=_rI_0)*($g_qsz="2")
         *($g_q_0_0=_q_0_0)
         *($g_q_0_1=_q_0_1)
         *($g_q_1_0=_q_1_0)
         *($g_q_1_1=_q_1_1)
         *($g_state="HasNextinvalid")
         *(_rI_1_1=_rI_0))
        ||(($g_q_0_0=_q_0_0)
          *($g_q_1_1!=true)
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
          *($g_q_1_1!=true)
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
      }+{()}
      ($g_qsz,$g_rI,$g_qsz
      ,$g_q_0_1,$g_q_0_0)
      {(($g_state="HasNextstart")
       *($g_q_0_1=_q_1_1)
       *($g_q_0_0=_q_1_0)
       *($g_rI=_rI_1_1)
       *($g_qsz="1"))
      }
    procedure enqueue_$$ :
      {($g_qsz="0")}
      ($g_qsz,$g_q_0_0
      ,$g_q_0_1)
      {(($g_qsz="1")
       *($g_q_0_0=@parameter0:)
       *($g_q_0_1=@parameter1:))
      }+{($g_qsz="1")}
      ($g_qsz,$g_q_1_0
      ,$g_q_1_1)
      {(($g_qsz="2")
       *($g_q_1_0=@parameter0:)
       *($g_q_1_1=@parameter1:))
      }


    procedure HasNext.print$$java.util.Iterator$$void :
      
    ?
      call 
        :=emit_$$("call_$$_HasNext.print$$java.util.Iterator$$void"
                 ,@parameter0:);
      call :=HasNext.print$$java.util.Iterator$$void_I(@parameter0:);
      call :=emit_$$("return_$$_HasNext.print$$java.util.Iterator$$void");
    procedure HasNext.print$$java.util.Iterator$$void_I :
      
    ?
      assign r0:={()}(){($ret_v0=@parameter0:)}();
      call $temp:=java.util.Iterator.hasNext$$$$boolean();
      assign $z0:={()}(){($ret_v0=$temp)}();
      goto gen_1,gen_2;
      label gen_1;
      assign :={()}(){($z0=0)}();
      goto label0;
      label gen_2;
      assign :={()}(){($z0!=0)}();
      call :=java.util.Iterator.next$$$$java.lang.Object();
      label label0;
      nop;
    procedure java.util.Iterator.hasNext$$$$boolean :
      
    ?
      call :=emit_$$("call_$$_java.util.Iterator.hasNext$$$$boolean");
      call $ret_v0:=java.util.Iterator.hasNext$$$$boolean_I();
      call :=emit_$$("return_$$_java.util.Iterator.hasNext$$$$boolean");
    procedure java.util.Iterator.hasNext$$$$boolean_I :
    procedure java.util.Iterator.next$$$$java.lang.Object :
      
    ?
      call :=emit_$$("call_$$_java.util.Iterator.next$$$$java.lang.Object");
      call $ret_v0:=java.util.Iterator.next$$$$java.lang.Object_I();
      call 
        :=emit_$$("return_$$_java.util.Iterator.next$$$$java.lang.Object");
    procedure java.util.Iterator.next$$$$java.lang.Object_I :
  
