// Test for speed.
    procedure emit_$$ :
      
    ?
      call :=enqueue_$$(@parameter0:,@parameter1:);
      call :=step_$$();
      assign :={(($g_current_automaton_state!="HasNexterror"))}()
        {(($g_current_automaton_state!="HasNexterror"))}();
    procedure step_$$ :
      {((($g_register_i=_log_register_i_0)
         * ($g_queue_event_0_position_0
           !="call_$$_java.util.Iterator.next$$$$java.lang.Object")
         * ($g_queue_event_1_position_0
           !="return_$$_java.util.Iterator.hasNext$$$$boolean")
         * ($g_current_automaton_state="HasNextinvalid")
         * ($g_current_queue_list_size=2)
         * ($g_queue_event_1_position_1=_log_queue_1_1)
         * ($g_queue_event_0_position_1=_log_queue_0_1)
         * ($g_queue_event_1_position_0=_log_queue_1_0)
         * ($g_queue_event_0_position_0=_log_queue_0_0)
         * (_log_register_i_1_trans_1=_log_register_i_0))
        || (($g_queue_event_0_position_0=_log_queue_0_0)
            * ($g_queue_event_0_position_1!=_log_register_i_0)
            * ($g_queue_event_0_position_1=_log_queue_0_1)
            * ($g_register_i=_log_register_i_0)
            * ($g_current_queue_list_size=2)
            * ($g_current_automaton_state="HasNextinvalid")
            * ($g_queue_event_1_position_0=_log_queue_1_0)
            * ($g_queue_event_0_position_0
              !="call_$$_java.util.Iterator.next$$$$java.lang.Object")
            * ($g_queue_event_1_position_1=_log_queue_1_1))
        || (($g_register_i=_log_register_i_0)
            * ($g_queue_event_1_position_0
              !="return_$$_java.util.Iterator.hasNext$$$$boolean")
            * ($g_current_automaton_state="HasNextinvalid")
            * ($g_queue_event_0_position_1!=_log_register_i_0)
            * ($g_current_queue_list_size=2)
            * ($g_queue_event_1_position_1=_log_queue_1_1)
            * ($g_queue_event_0_position_1=_log_queue_0_1)
            * ($g_queue_event_1_position_0=_log_queue_1_0)
            * ($g_queue_event_0_position_0=_log_queue_0_0)
            * (_log_register_i_1_trans_1=_log_register_i_0))
        || (($g_register_i=_log_register_i_0)
            * ($g_current_automaton_state="HasNextinvalid")
            * ($g_queue_event_0_position_1!=_log_register_i_0)
            * ($g_current_queue_list_size=2)
            * ($g_queue_event_1_position_1=0)
            * ($g_queue_event_1_position_1=_log_queue_1_1)
            * ($g_queue_event_0_position_1=_log_queue_0_1)
            * ($g_queue_event_1_position_0=_log_queue_1_0)
            * ($g_queue_event_0_position_0=_log_queue_0_0)
            * (_log_register_i_1_trans_1=_log_register_i_0))
        || (($g_queue_event_0_position_0=_log_queue_0_0)
            * ($g_queue_event_0_position_1!=_log_register_i_0)
            * ($g_queue_event_0_position_1=_log_queue_0_1)
            * ($g_register_i=_log_register_i_0)
            * ($g_current_queue_list_size=2)
            * ($g_current_automaton_state="HasNextinvalid")
            * ($g_queue_event_1_position_0=_log_queue_1_0)
            * ($g_queue_event_1_position_1=_log_queue_1_1)
            * ($g_queue_event_0_position_0
              !="call_$$_java.util.Iterator.hasNext$$$$boolean"))
        || (($g_register_i=_log_register_i_0)
            * ($g_queue_event_0_position_0
              !="call_$$_java.util.Iterator.next$$$$java.lang.Object")
            * ($g_current_automaton_state="HasNextinvalid")
            * ($g_current_queue_list_size=2)
            * ($g_queue_event_1_position_1=0)
            * ($g_queue_event_1_position_1=_log_queue_1_1)
            * ($g_queue_event_0_position_1=_log_queue_0_1)
            * ($g_queue_event_1_position_0=_log_queue_1_0)
            * ($g_queue_event_0_position_0=_log_queue_0_0)
            * (_log_register_i_1_trans_1=_log_register_i_0))
        || (($g_register_i=_log_register_i_0)
            * ($g_queue_event_0_position_0=_log_queue_0_0)
            * ($g_queue_event_0_position_1=_log_queue_0_1)
            * ($g_queue_event_0_position_1!=_log_register_i_0)
            * ($g_queue_event_1_position_0=_log_queue_1_0)
            * ($g_queue_event_1_position_1=_log_queue_1_1)
            * ($g_current_queue_list_size=2)
            * ($g_current_automaton_state="HasNextinvalid"))
        || (($g_queue_event_0_position_0=_log_queue_0_0)
            * ($g_queue_event_0_position_1=_log_queue_0_1)
            * ($g_register_i=_log_register_i_0)
            * ($g_current_queue_list_size=2)
            * ($g_current_automaton_state="HasNextinvalid")
            * ($g_queue_event_1_position_0=_log_queue_1_0)
            * ($g_queue_event_0_position_0
              !="call_$$_java.util.Iterator.next$$$$java.lang.Object")
            * ($g_queue_event_1_position_1=_log_queue_1_1)
            * ($g_queue_event_0_position_0
              !="call_$$_java.util.Iterator.hasNext$$$$boolean")))}
      ($g_current_queue_list_size,$g_queue_event_0_position_1
      ,$g_queue_event_0_position_0)
      {(($g_register_i=_log_register_i_0) * ($g_current_queue_list_size=1)
        * ($g_queue_event_0_position_1=_log_queue_1_1)
        * ($g_current_automaton_state="HasNextinvalid")
        * ($g_queue_event_0_position_0=_log_queue_1_0))}
      +{((($g_register_i=_log_register_i_0)
          * ($g_queue_event_0_position_0
            !="return_$$_java.util.Collection.iterator$$$$java.util.Iterator")
          * ($g_current_queue_list_size=2)
          * ($g_current_automaton_state="HasNextstart")
          * ($g_queue_event_1_position_1=_log_queue_1_1)
          * ($g_queue_event_0_position_1=_log_queue_0_1)
          * ($g_queue_event_1_position_0=_log_queue_1_0)
          * ($g_queue_event_0_position_0=_log_queue_0_0)
          * (_log_register_i_1_trans_1=_log_register_i_0)
          * ($g_queue_event_0_position_0
            ="return_$$_java.util.Iterator.hasNext$$$$boolean"))
         || (($g_register_i=_log_register_i_0)
             * ($g_queue_event_0_position_0
               !="return_$$_java.util.Collection.iterator$$$$java.util.Iterator")
             * ($g_current_queue_list_size=2)
             * ($g_current_automaton_state="HasNextstart")
             * ($g_queue_event_1_position_1=_log_queue_1_1)
             * ($g_queue_event_0_position_1=_log_queue_0_1)
             * ($g_queue_event_1_position_0=_log_queue_1_0)
             * ($g_queue_event_0_position_0=_log_queue_0_0)
             * ($g_queue_event_0_position_0
               ="call_$$_java.util.Collection.iterator$$$$java.util.Iterator")
             * (_log_register_i_1_trans_1=_log_register_i_0))
         || (($g_register_i=_log_register_i_0)
             * ($g_queue_event_0_position_0
               ="return_$$_java.util.Iterator.next$$$$java.lang.Object")
             * ($g_queue_event_0_position_0
               !="return_$$_java.util.Collection.iterator$$$$java.util.Iterator")
             * ($g_current_queue_list_size=2)
             * ($g_current_automaton_state="HasNextstart")
             * ($g_queue_event_1_position_1=_log_queue_1_1)
             * ($g_queue_event_0_position_1=_log_queue_0_1)
             * ($g_queue_event_1_position_0=_log_queue_1_0)
             * ($g_queue_event_0_position_0=_log_queue_0_0)
             * (_log_register_i_1_trans_1=_log_register_i_0))
         || (($g_register_i=_log_register_i_0)
             * ($g_queue_event_0_position_0
               ="return_$$_java.util.Collection.iterator$$$$java.util.Iterator")
             * ($g_queue_event_0_position_0
               !="return_$$_java.util.Collection.iterator$$$$java.util.Iterator")
             * ($g_current_queue_list_size=2)
             * ($g_current_automaton_state="HasNextstart")
             * ($g_queue_event_1_position_1=_log_queue_1_1)
             * ($g_queue_event_0_position_1=_log_queue_0_1)
             * ($g_queue_event_1_position_0=_log_queue_1_0)
             * ($g_queue_event_0_position_0=_log_queue_0_0)
             * (_log_register_i_1_trans_1=_log_register_i_0))
         || (($g_register_i=_log_register_i_0)
             * ($g_queue_event_0_position_0
               ="call_$$_java.util.Iterator.hasNext$$$$boolean")
             * ($g_queue_event_0_position_0
               !="return_$$_java.util.Collection.iterator$$$$java.util.Iterator")
             * ($g_current_queue_list_size=2)
             * ($g_current_automaton_state="HasNextstart")
             * ($g_queue_event_1_position_1=_log_queue_1_1)
             * ($g_queue_event_0_position_1=_log_queue_0_1)
             * ($g_queue_event_1_position_0=_log_queue_1_0)
             * ($g_queue_event_0_position_0=_log_queue_0_0)
             * (_log_register_i_1_trans_1=_log_register_i_0))
         || (($g_register_i=_log_register_i_0)
             * ($g_queue_event_0_position_0
               !="return_$$_java.util.Collection.iterator$$$$java.util.Iterator")
             * ($g_current_queue_list_size=2)
             * ($g_current_automaton_state="HasNextstart")
             * ($g_queue_event_1_position_1=_log_queue_1_1)
             * ($g_queue_event_0_position_1=_log_queue_0_1)
             * ($g_queue_event_1_position_0=_log_queue_1_0)
             * ($g_queue_event_0_position_0=_log_queue_0_0)
             * ($g_queue_event_0_position_0
               ="call_$$_java.util.Iterator.next$$$$java.lang.Object")
             * (_log_register_i_1_trans_1=_log_register_i_0)))}
      ($g_current_queue_list_size,$g_register_i,$g_current_queue_list_size
      ,$g_queue_event_0_position_1,$g_queue_event_0_position_0)
      {(($g_current_automaton_state="HasNextstart")
        * ($g_current_queue_list_size=1)
        * ($g_queue_event_0_position_1=_log_queue_1_1)
        * ($g_queue_event_0_position_0=_log_queue_1_0)
        * ($g_register_i=_log_register_i_1_trans_1))}
      +
      {(($g_register_i=_log_register_i_0)
         * ($g_queue_event_0_position_1=_log_queue_0_1)
         * ($g_current_automaton_state="HasNextinvalid")
         * ($g_queue_event_0_position_0=_log_queue_0_0)
         * (_log_register_i_1_trans_1=_log_register_i_0)
         * ($g_current_queue_list_size=2)
         * ($g_queue_event_0_position_1=_log_register_i_0)
         * (_log_register_i_1_trans_0=_log_register_i_0)
         * ($g_queue_event_1_position_0
           ="return_$$_java.util.Iterator.hasNext$$$$boolean")
         * ($g_queue_event_1_position_1=_log_queue_1_1)
         * ($g_queue_event_0_position_0
           ="call_$$_java.util.Iterator.hasNext$$$$boolean")
         * ($g_queue_event_1_position_0=_log_queue_1_0)
         * (_log_register_i_2_trans_1=_log_register_i_1_trans_1)
         * ($g_queue_event_0_position_0
           ="call_$$_java.util.Iterator.next$$$$java.lang.Object")
         * ($g_queue_event_1_position_1!=0))}
      ($g_current_queue_list_size,$g_current_automaton_state,$g_register_i
      ,$g_current_queue_list_size,$g_current_queue_list_size
      ,$g_current_automaton_state,$g_register_i,$g_current_queue_list_size
      ,$g_queue_event_0_position_1,$g_queue_event_0_position_0)
      {((($g_register_i=_log_register_i_2_trans_1)
         * ($g_current_queue_list_size=0)
         * ($g_current_automaton_state="HasNextvalid"))
        || (($g_current_queue_list_size=1)
            * ($g_queue_event_0_position_1=_log_queue_1_1)
            * ($g_queue_event_0_position_0=_log_queue_1_0)
            * ($g_current_automaton_state="HasNexterror")
            * ($g_register_i=_log_register_i_1_trans_0)))}
      +{(($g_current_automaton_state="HasNexterror")
         * ($g_queue_event_1_position_1=_log_queue_1_1)
         * ($g_register_i=_log_register_i_0)
         * ($g_queue_event_1_position_0=_log_queue_1_0)
         * ($g_queue_event_0_position_1=_log_queue_0_1)
         * ($g_current_queue_list_size=2)
         * ($g_queue_event_0_position_0=_log_queue_0_0))}
      ($g_current_queue_list_size,$g_queue_event_0_position_1
      ,$g_queue_event_0_position_0)
      {(($g_register_i=_log_register_i_0) * ($g_current_queue_list_size=1)
        * ($g_queue_event_0_position_1=_log_queue_1_1)
        * ($g_queue_event_0_position_0=_log_queue_1_0)
        * ($g_current_automaton_state="HasNexterror"))}
      +{((($g_register_i=_log_register_i_0)
          * ($g_queue_event_0_position_1=_log_queue_0_1)
          * ($g_queue_event_0_position_0=_log_queue_0_0)
          * ($g_current_automaton_state="HasNextvalid")
          * ($g_queue_event_1_position_1=_log_queue_1_1)
          * ($g_queue_event_1_position_0=_log_queue_1_0)
          * ($g_queue_event_0_position_0
            !="call_$$_java.util.Iterator.next$$$$java.lang.Object")
          * ($g_current_queue_list_size=2))
         || (($g_register_i=_log_register_i_0)
             * ($g_queue_event_0_position_1=_log_queue_0_1)
             * ($g_queue_event_0_position_0=_log_queue_0_0)
             * ($g_current_automaton_state="HasNextvalid")
             * ($g_queue_event_1_position_1=_log_queue_1_1)
             * ($g_queue_event_1_position_0=_log_queue_1_0)
             * ($g_queue_event_0_position_1!=_log_register_i_0)
             * ($g_current_queue_list_size=2)))}
      ($g_current_queue_list_size,$g_queue_event_0_position_1
      ,$g_queue_event_0_position_0)
      {(($g_register_i=_log_register_i_0) * ($g_current_queue_list_size=1)
        * ($g_queue_event_0_position_1=_log_queue_1_1)
        * ($g_queue_event_0_position_0=_log_queue_1_0)
        * ($g_current_automaton_state="HasNextvalid"))}
      +{(($g_current_queue_list_size=2)
         * ($g_queue_event_0_position_0
           !="call_$$_java.util.Collection.iterator$$$$java.util.Iterator")
         * ($g_queue_event_1_position_0=_log_queue_1_0)
         * ($g_current_automaton_state="HasNextstart")
         * ($g_queue_event_0_position_0
           !="return_$$_java.util.Collection.iterator$$$$java.util.Iterator")
         * ($g_queue_event_0_position_0=_log_queue_0_0)
         * ($g_queue_event_0_position_0
           !="call_$$_java.util.Iterator.hasNext$$$$boolean")
         * ($g_register_i=_log_register_i_0)
         * ($g_queue_event_1_position_1=_log_queue_1_1)
         * ($g_queue_event_0_position_0
           !="call_$$_java.util.Iterator.next$$$$java.lang.Object")
         * ($g_queue_event_0_position_1=_log_queue_0_1)
         * ($g_queue_event_0_position_0
           !="return_$$_java.util.Iterator.next$$$$java.lang.Object")
         * ($g_queue_event_0_position_0
           !="return_$$_java.util.Iterator.hasNext$$$$boolean"))}
      ($g_current_queue_list_size,$g_queue_event_0_position_1
      ,$g_queue_event_0_position_0)
      {(($g_current_automaton_state="HasNextstart")
        * ($g_register_i=_log_register_i_0) * ($g_current_queue_list_size=1)
        * ($g_queue_event_0_position_1=_log_queue_1_1)
        * ($g_queue_event_0_position_0=_log_queue_1_0))}
      +{((($g_queue_event_0_position_0
          ="return_$$_java.util.Collection.iterator$$$$java.util.Iterator")
          * (_log_register_i_1_trans_1=_log_register_i_0)
          * (_log_register_i_1_trans_0=$g_queue_event_0_position_1)
          * ($g_register_i=_log_register_i_0)
          * ($g_current_queue_list_size=2)
          * ($g_queue_event_1_position_0=_log_queue_1_0)
          * ($g_queue_event_0_position_0
            ="call_$$_java.util.Iterator.hasNext$$$$boolean")
          * ($g_queue_event_0_position_0=_log_queue_0_0)
          * ($g_queue_event_1_position_1=_log_queue_1_1)
          * ($g_current_automaton_state="HasNextstart")
          * ($g_queue_event_0_position_1=_log_queue_0_1))
         || (($g_queue_event_0_position_0
             ="return_$$_java.util.Collection.iterator$$$$java.util.Iterator")
             * (_log_register_i_1_trans_1=_log_register_i_0)
             * (_log_register_i_1_trans_0=$g_queue_event_0_position_1)
             * ($g_register_i=_log_register_i_0)
             * ($g_current_queue_list_size=2)
             * ($g_queue_event_1_position_0=_log_queue_1_0)
             * ($g_queue_event_0_position_0=_log_queue_0_0)
             * ($g_queue_event_1_position_1=_log_queue_1_1)
             * ($g_current_automaton_state="HasNextstart")
             * ($g_queue_event_0_position_1=_log_queue_0_1)
             * ($g_queue_event_0_position_0
               ="call_$$_java.util.Iterator.next$$$$java.lang.Object"))
         || (($g_queue_event_0_position_0
             ="return_$$_java.util.Collection.iterator$$$$java.util.Iterator")
             * (_log_register_i_1_trans_1=_log_register_i_0)
             * (_log_register_i_1_trans_0=$g_queue_event_0_position_1)
             * ($g_register_i=_log_register_i_0)
             * ($g_current_queue_list_size=2)
             * ($g_queue_event_1_position_0=_log_queue_1_0)
             * ($g_queue_event_0_position_0
               ="return_$$_java.util.Iterator.next$$$$java.lang.Object")
             * ($g_queue_event_0_position_0=_log_queue_0_0)
             * ($g_queue_event_1_position_1=_log_queue_1_1)
             * ($g_current_automaton_state="HasNextstart")
             * ($g_queue_event_0_position_1=_log_queue_0_1))
         || (($g_queue_event_0_position_0
             ="return_$$_java.util.Collection.iterator$$$$java.util.Iterator")
             * (_log_register_i_1_trans_1=_log_register_i_0)
             * (_log_register_i_1_trans_0=$g_queue_event_0_position_1)
             * ($g_register_i=_log_register_i_0)
             * ($g_current_queue_list_size=2)
             * ($g_queue_event_1_position_0=_log_queue_1_0)
             * ($g_queue_event_0_position_0
               ="call_$$_java.util.Collection.iterator$$$$java.util.Iterator")
             * ($g_queue_event_0_position_0=_log_queue_0_0)
             * ($g_queue_event_1_position_1=_log_queue_1_1)
             * ($g_current_automaton_state="HasNextstart")
             * ($g_queue_event_0_position_1=_log_queue_0_1))
         || (($g_queue_event_0_position_0
             ="return_$$_java.util.Collection.iterator$$$$java.util.Iterator")
             * (_log_register_i_1_trans_1=_log_register_i_0)
             * (_log_register_i_1_trans_0=$g_queue_event_0_position_1)
             * ($g_register_i=_log_register_i_0)
             * ($g_current_queue_list_size=2)
             * ($g_queue_event_1_position_0=_log_queue_1_0)
             * ($g_queue_event_0_position_0=_log_queue_0_0)
             * ($g_queue_event_1_position_1=_log_queue_1_1)
             * ($g_current_automaton_state="HasNextstart")
             * ($g_queue_event_0_position_0
               ="return_$$_java.util.Iterator.hasNext$$$$boolean")
             * ($g_queue_event_0_position_1=_log_queue_0_1))
         || (($g_queue_event_0_position_0
             ="return_$$_java.util.Collection.iterator$$$$java.util.Iterator")
             * ($g_register_i=_log_register_i_0)
             * ($g_current_queue_list_size=2)
             * ($g_current_automaton_state="HasNextstart")
             * ($g_queue_event_1_position_1=_log_queue_1_1)
             * ($g_queue_event_0_position_1=_log_queue_0_1)
             * ($g_queue_event_1_position_0=_log_queue_1_0)
             * ($g_queue_event_0_position_0=_log_queue_0_0)
             * (_log_register_i_1_trans_1=_log_register_i_0)
             * (_log_register_i_1_trans_0=$g_queue_event_0_position_1)))}
      ($g_current_queue_list_size,$g_register_i,$g_current_queue_list_size
      ,$g_queue_event_0_position_1,$g_queue_event_0_position_0
      ,$g_current_queue_list_size,$g_current_automaton_state,$g_register_i
      ,$g_current_queue_list_size,$g_queue_event_0_position_1
      ,$g_queue_event_0_position_0)
      {((($g_current_automaton_state="HasNextstart")
         * ($g_current_queue_list_size=1)
         * ($g_queue_event_0_position_1=_log_queue_1_1)
         * ($g_queue_event_0_position_0=_log_queue_1_0)
         * ($g_register_i=_log_register_i_1_trans_1))
        || (($g_current_queue_list_size=1)
            * ($g_queue_event_0_position_1=_log_queue_1_1)
            * ($g_current_automaton_state="HasNextinvalid")
            * ($g_queue_event_0_position_0=_log_queue_1_0)
            * ($g_register_i=_log_register_i_1_trans_0)))}
      +{(($g_register_i=_log_register_i_0)
         * ($g_queue_event_0_position_1=_log_queue_0_1)
         * ($g_queue_event_0_position_0
           !="return_$$_java.util.Collection.iterator$$$$java.util.Iterator")
         * ($g_queue_event_0_position_0=_log_queue_0_0)
         * ($g_current_queue_list_size=2)
         * ($g_queue_event_0_position_0
           !="call_$$_java.util.Iterator.next$$$$java.lang.Object")
         * ($g_queue_event_1_position_1=_log_queue_1_1)
         * ($g_queue_event_0_position_0
           !="return_$$_java.util.Iterator.hasNext$$$$boolean")
         * ($g_queue_event_1_position_0=_log_queue_1_0)
         * (_log_register_i_1_trans_0=$g_queue_event_0_position_1)
         * ($g_current_automaton_state="HasNextstart")
         * ($g_queue_event_0_position_0
           ="return_$$_java.util.Collection.iterator$$$$java.util.Iterator")
         * ($g_queue_event_0_position_0
           !="call_$$_java.util.Collection.iterator$$$$java.util.Iterator")
         * ($g_queue_event_0_position_0
           !="return_$$_java.util.Iterator.next$$$$java.lang.Object")
         * ($g_queue_event_0_position_0
           !="call_$$_java.util.Iterator.hasNext$$$$boolean"))}
      ($g_current_queue_list_size,$g_current_automaton_state,$g_register_i
      ,$g_current_queue_list_size,$g_queue_event_0_position_1
      ,$g_queue_event_0_position_0)
      {(($g_current_queue_list_size=1)
        * ($g_queue_event_0_position_1=_log_queue_1_1)
        * ($g_current_automaton_state="HasNextinvalid")
        * ($g_queue_event_0_position_0=_log_queue_1_0)
        * ($g_register_i=_log_register_i_1_trans_0))}
      +{((($g_register_i=_log_register_i_0) * ($g_current_queue_list_size=2)
          * ($g_queue_event_1_position_0=_log_queue_1_0)
          * (_log_register_i_1_trans_0=_log_register_i_0)
          * ($g_queue_event_0_position_0
            !="call_$$_java.util.Iterator.hasNext$$$$boolean")
          * ($g_queue_event_0_position_0=_log_queue_0_0)
          * ($g_queue_event_1_position_1=_log_queue_1_1)
          * ($g_queue_event_0_position_1=_log_register_i_0)
          * ($g_current_automaton_state="HasNextinvalid")
          * ($g_queue_event_0_position_1=_log_queue_0_1)
          * ($g_queue_event_0_position_0
            ="call_$$_java.util.Iterator.next$$$$java.lang.Object"))
         || (($g_register_i=_log_register_i_0)
             * ($g_queue_event_1_position_1=_log_queue_1_1)
             * ($g_current_automaton_state="HasNextinvalid")
             * (_log_register_i_1_trans_0=_log_register_i_0)
             * ($g_queue_event_0_position_0
               ="call_$$_java.util.Iterator.next$$$$java.lang.Object")
             * ($g_queue_event_1_position_0
               !="return_$$_java.util.Iterator.hasNext$$$$boolean")
             * ($g_queue_event_0_position_0=_log_queue_0_0)
             * (_log_register_i_1_trans_1=_log_register_i_0)
             * ($g_queue_event_1_position_0=_log_queue_1_0)
             * ($g_queue_event_0_position_1=_log_register_i_0)
             * ($g_current_queue_list_size=2)
             * ($g_queue_event_0_position_1=_log_queue_0_1))
         || (($g_register_i=_log_register_i_0)
             * ($g_queue_event_1_position_1=_log_queue_1_1)
             * ($g_current_automaton_state="HasNextinvalid")
             * (_log_register_i_1_trans_0=_log_register_i_0)
             * ($g_queue_event_0_position_0
               ="call_$$_java.util.Iterator.next$$$$java.lang.Object")
             * ($g_queue_event_1_position_1=0)
             * ($g_queue_event_0_position_0=_log_queue_0_0)
             * (_log_register_i_1_trans_1=_log_register_i_0)
             * ($g_queue_event_1_position_0=_log_queue_1_0)
             * ($g_queue_event_0_position_1=_log_register_i_0)
             * ($g_current_queue_list_size=2)
             * ($g_queue_event_0_position_1=_log_queue_0_1))
         || (($g_register_i=_log_register_i_0)
             * ($g_current_queue_list_size=2)
             * ($g_queue_event_1_position_0=_log_queue_1_0)
             * (_log_register_i_1_trans_0=_log_register_i_0)
             * ($g_queue_event_0_position_0=_log_queue_0_0)
             * ($g_queue_event_1_position_1=_log_queue_1_1)
             * ($g_queue_event_0_position_1=_log_register_i_0)
             * ($g_queue_event_0_position_1!=_log_register_i_0)
             * ($g_current_automaton_state="HasNextinvalid")
             * ($g_queue_event_0_position_1=_log_queue_0_1)
             * ($g_queue_event_0_position_0
               ="call_$$_java.util.Iterator.next$$$$java.lang.Object")))}
      ($g_current_queue_list_size,$g_current_automaton_state,$g_register_i
      ,$g_current_queue_list_size,$g_queue_event_0_position_1
      ,$g_queue_event_0_position_0)
      {(($g_current_queue_list_size=1)
        * ($g_queue_event_0_position_1=_log_queue_1_1)
        * ($g_queue_event_0_position_0=_log_queue_1_0)
        * ($g_current_automaton_state="HasNexterror")
        * ($g_register_i=_log_register_i_1_trans_0))}
      +{((($g_queue_event_1_position_1!=0)
          * ($g_queue_event_1_position_1=_log_queue_1_1)
          * ($g_queue_event_0_position_1=_log_register_i_0)
          * ($g_current_automaton_state="HasNextinvalid")
          * ($g_queue_event_0_position_1=_log_queue_0_1)
          * ($g_queue_event_1_position_0
            ="return_$$_java.util.Iterator.hasNext$$$$boolean")
          * ($g_queue_event_0_position_0
            ="call_$$_java.util.Iterator.hasNext$$$$boolean")
          * ($g_register_i=_log_register_i_0)
          * ($g_queue_event_1_position_0=_log_queue_1_0)
          * ($g_queue_event_0_position_0
            !="call_$$_java.util.Iterator.next$$$$java.lang.Object")
          * (_log_register_i_1_trans_1=_log_register_i_0)
          * ($g_current_queue_list_size=2)
          * ($g_queue_event_0_position_0=_log_queue_0_0)
          * (_log_register_i_2_trans_1=_log_register_i_1_trans_1))
         || (($g_queue_event_1_position_1!=0)
             * ($g_queue_event_1_position_1=_log_queue_1_1)
             * ($g_queue_event_0_position_1!=_log_register_i_0)
             * ($g_queue_event_0_position_1=_log_register_i_0)
             * ($g_current_automaton_state="HasNextinvalid")
             * ($g_queue_event_0_position_1=_log_queue_0_1)
             * ($g_queue_event_1_position_0
               ="return_$$_java.util.Iterator.hasNext$$$$boolean")
             * ($g_queue_event_0_position_0
               ="call_$$_java.util.Iterator.hasNext$$$$boolean")
             * ($g_register_i=_log_register_i_0)
             * ($g_queue_event_1_position_0=_log_queue_1_0)
             * (_log_register_i_1_trans_1=_log_register_i_0)
             * ($g_current_queue_list_size=2)
             * ($g_queue_event_0_position_0=_log_queue_0_0)
             * (_log_register_i_2_trans_1=_log_register_i_1_trans_1)))}
      ($g_current_queue_list_size,$g_current_automaton_state,$g_register_i
      ,$g_current_queue_list_size)
      {(($g_register_i=_log_register_i_2_trans_1)
        * ($g_current_queue_list_size=0)
        * ($g_current_automaton_state="HasNextvalid"))}
      +{(($g_register_i=_log_register_i_0)
         * (_log_register_i_1_trans_0=_log_register_i_0)
         * ($g_queue_event_0_position_1=_log_register_i_0)
         * ($g_current_queue_list_size=2)
         * ($g_queue_event_1_position_1=_log_queue_1_1)
         * ($g_queue_event_0_position_1=_log_queue_0_1)
         * ($g_queue_event_1_position_0=_log_queue_1_0)
         * ($g_queue_event_0_position_0=_log_queue_0_0)
         * ($g_queue_event_0_position_0
           ="call_$$_java.util.Iterator.next$$$$java.lang.Object")
         * ($g_current_automaton_state="HasNextvalid"))}
      ($g_current_queue_list_size,$g_current_automaton_state,$g_register_i
      ,$g_current_queue_list_size,$g_queue_event_0_position_1
      ,$g_queue_event_0_position_0)
      {(($g_current_queue_list_size=1)
        * ($g_queue_event_0_position_1=_log_queue_1_1)
        * ($g_current_automaton_state="HasNextinvalid")
        * ($g_queue_event_0_position_0=_log_queue_1_0)
        * ($g_register_i=_log_register_i_1_trans_0))}
    procedure enqueue_$$ :
      {($g_current_queue_list_size=1)}
      ($g_current_queue_list_size,$g_queue_event_1_position_0
      ,$g_queue_event_1_position_1)
      {(($g_queue_event_1_position_1=@parameter1:)
        * ($g_current_queue_list_size=2)
        * ($g_queue_event_1_position_0=@parameter0:))}
      +{($g_current_queue_list_size=0)}
      ($g_current_queue_list_size,$g_queue_event_0_position_0
      ,$g_queue_event_0_position_1)
      {(($g_queue_event_0_position_1=@parameter1:)
        * ($g_current_queue_list_size=1)
        * ($g_queue_event_0_position_0=@parameter0:))}


procedure java.util.ArrayList.ensureCapacity$$int$$void :
  
?
  call :=emit_$$("call_$$_java.util.ArrayList.ensureCapacity$$int$$void");
  call :=java.util.ArrayList.ensureCapacity$$int$$void_I();
  call 
    :=emit_$$("return_$$_java.util.ArrayList.ensureCapacity$$int$$void");

procedure java.util.ArrayList.ensureCapacity$$int$$void_I :
  
?
  assign r0:={emp}(){($ret_v0=@this:)}();
  assign i0:={emp}(){($ret_v0=@parameter0:)}();
  goto gen_7,gen_8;
  label gen_7;
  assign :={emp}(){i0 <= 0}();
  goto label0;
  label gen_8;
  assign :={emp}(){i0 > 0}();
  label label0;
  nop;

