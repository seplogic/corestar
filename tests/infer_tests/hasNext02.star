// Test for speed.
    procedure emit_$$ 
      
    :
      call enqueue_$$(@parameter0,@parameter1);
      call step_$$();
      spec {((@current_automaton_state!="HasNexterror"))}()
        {((@current_automaton_state!="HasNexterror"))};
    procedure step_$$ 
      {(((@register_i=_log_register_i_0)
         * (@queue_event_0_position_0
           !="call_$$_java.util.Iterator.next$$$$java.lang.Object")
         * (@queue_event_1_position_0
           !="return_$$_java.util.Iterator.hasNext$$$$boolean")
         * (@current_automaton_state="HasNextinvalid")
         * (@current_queue_list_size=2)
         * (@queue_event_1_position_1=_log_queue_1_1)
         * (@queue_event_0_position_1=_log_queue_0_1)
         * (@queue_event_1_position_0=_log_queue_1_0)
         * (@queue_event_0_position_0=_log_queue_0_0)
         * (_log_register_i_1_trans_1=_log_register_i_0))
        || ((@queue_event_0_position_0=_log_queue_0_0)
            * (@queue_event_0_position_1!=_log_register_i_0)
            * (@queue_event_0_position_1=_log_queue_0_1)
            * (@register_i=_log_register_i_0)
            * (@current_queue_list_size=2)
            * (@current_automaton_state="HasNextinvalid")
            * (@queue_event_1_position_0=_log_queue_1_0)
            * (@queue_event_0_position_0
              !="call_$$_java.util.Iterator.next$$$$java.lang.Object")
            * (@queue_event_1_position_1=_log_queue_1_1))
        || ((@register_i=_log_register_i_0)
            * (@queue_event_1_position_0
              !="return_$$_java.util.Iterator.hasNext$$$$boolean")
            * (@current_automaton_state="HasNextinvalid")
            * (@queue_event_0_position_1!=_log_register_i_0)
            * (@current_queue_list_size=2)
            * (@queue_event_1_position_1=_log_queue_1_1)
            * (@queue_event_0_position_1=_log_queue_0_1)
            * (@queue_event_1_position_0=_log_queue_1_0)
            * (@queue_event_0_position_0=_log_queue_0_0)
            * (_log_register_i_1_trans_1=_log_register_i_0))
        || ((@register_i=_log_register_i_0)
            * (@current_automaton_state="HasNextinvalid")
            * (@queue_event_0_position_1!=_log_register_i_0)
            * (@current_queue_list_size=2)
            * (@queue_event_1_position_1=0)
            * (@queue_event_1_position_1=_log_queue_1_1)
            * (@queue_event_0_position_1=_log_queue_0_1)
            * (@queue_event_1_position_0=_log_queue_1_0)
            * (@queue_event_0_position_0=_log_queue_0_0)
            * (_log_register_i_1_trans_1=_log_register_i_0))
        || ((@queue_event_0_position_0=_log_queue_0_0)
            * (@queue_event_0_position_1!=_log_register_i_0)
            * (@queue_event_0_position_1=_log_queue_0_1)
            * (@register_i=_log_register_i_0)
            * (@current_queue_list_size=2)
            * (@current_automaton_state="HasNextinvalid")
            * (@queue_event_1_position_0=_log_queue_1_0)
            * (@queue_event_1_position_1=_log_queue_1_1)
            * (@queue_event_0_position_0
              !="call_$$_java.util.Iterator.hasNext$$$$boolean"))
        || ((@register_i=_log_register_i_0)
            * (@queue_event_0_position_0
              !="call_$$_java.util.Iterator.next$$$$java.lang.Object")
            * (@current_automaton_state="HasNextinvalid")
            * (@current_queue_list_size=2)
            * (@queue_event_1_position_1=0)
            * (@queue_event_1_position_1=_log_queue_1_1)
            * (@queue_event_0_position_1=_log_queue_0_1)
            * (@queue_event_1_position_0=_log_queue_1_0)
            * (@queue_event_0_position_0=_log_queue_0_0)
            * (_log_register_i_1_trans_1=_log_register_i_0))
        || ((@register_i=_log_register_i_0)
            * (@queue_event_0_position_0=_log_queue_0_0)
            * (@queue_event_0_position_1=_log_queue_0_1)
            * (@queue_event_0_position_1!=_log_register_i_0)
            * (@queue_event_1_position_0=_log_queue_1_0)
            * (@queue_event_1_position_1=_log_queue_1_1)
            * (@current_queue_list_size=2)
            * (@current_automaton_state="HasNextinvalid"))
        || ((@queue_event_0_position_0=_log_queue_0_0)
            * (@queue_event_0_position_1=_log_queue_0_1)
            * (@register_i=_log_register_i_0)
            * (@current_queue_list_size=2)
            * (@current_automaton_state="HasNextinvalid")
            * (@queue_event_1_position_0=_log_queue_1_0)
            * (@queue_event_0_position_0
              !="call_$$_java.util.Iterator.next$$$$java.lang.Object")
            * (@queue_event_1_position_1=_log_queue_1_1)
            * (@queue_event_0_position_0
              !="call_$$_java.util.Iterator.hasNext$$$$boolean")))}
      (@current_queue_list_size,@queue_event_0_position_1
      ,@queue_event_0_position_0)
      {((@register_i=_log_register_i_0) * (@current_queue_list_size=1)
        * (@queue_event_0_position_1=_log_queue_1_1)
        * (@current_automaton_state="HasNextinvalid")
        * (@queue_event_0_position_0=_log_queue_1_0))}
      +{(((@register_i=_log_register_i_0)
          * (@queue_event_0_position_0
            !="return_$$_java.util.Collection.iterator$$$$java.util.Iterator")
          * (@current_queue_list_size=2)
          * (@current_automaton_state="HasNextstart")
          * (@queue_event_1_position_1=_log_queue_1_1)
          * (@queue_event_0_position_1=_log_queue_0_1)
          * (@queue_event_1_position_0=_log_queue_1_0)
          * (@queue_event_0_position_0=_log_queue_0_0)
          * (_log_register_i_1_trans_1=_log_register_i_0)
          * (@queue_event_0_position_0
            ="return_$$_java.util.Iterator.hasNext$$$$boolean"))
         || ((@register_i=_log_register_i_0)
             * (@queue_event_0_position_0
               !="return_$$_java.util.Collection.iterator$$$$java.util.Iterator")
             * (@current_queue_list_size=2)
             * (@current_automaton_state="HasNextstart")
             * (@queue_event_1_position_1=_log_queue_1_1)
             * (@queue_event_0_position_1=_log_queue_0_1)
             * (@queue_event_1_position_0=_log_queue_1_0)
             * (@queue_event_0_position_0=_log_queue_0_0)
             * (@queue_event_0_position_0
               ="call_$$_java.util.Collection.iterator$$$$java.util.Iterator")
             * (_log_register_i_1_trans_1=_log_register_i_0))
         || ((@register_i=_log_register_i_0)
             * (@queue_event_0_position_0
               ="return_$$_java.util.Iterator.next$$$$java.lang.Object")
             * (@queue_event_0_position_0
               !="return_$$_java.util.Collection.iterator$$$$java.util.Iterator")
             * (@current_queue_list_size=2)
             * (@current_automaton_state="HasNextstart")
             * (@queue_event_1_position_1=_log_queue_1_1)
             * (@queue_event_0_position_1=_log_queue_0_1)
             * (@queue_event_1_position_0=_log_queue_1_0)
             * (@queue_event_0_position_0=_log_queue_0_0)
             * (_log_register_i_1_trans_1=_log_register_i_0))
         || ((@register_i=_log_register_i_0)
             * (@queue_event_0_position_0
               ="return_$$_java.util.Collection.iterator$$$$java.util.Iterator")
             * (@queue_event_0_position_0
               !="return_$$_java.util.Collection.iterator$$$$java.util.Iterator")
             * (@current_queue_list_size=2)
             * (@current_automaton_state="HasNextstart")
             * (@queue_event_1_position_1=_log_queue_1_1)
             * (@queue_event_0_position_1=_log_queue_0_1)
             * (@queue_event_1_position_0=_log_queue_1_0)
             * (@queue_event_0_position_0=_log_queue_0_0)
             * (_log_register_i_1_trans_1=_log_register_i_0))
         || ((@register_i=_log_register_i_0)
             * (@queue_event_0_position_0
               ="call_$$_java.util.Iterator.hasNext$$$$boolean")
             * (@queue_event_0_position_0
               !="return_$$_java.util.Collection.iterator$$$$java.util.Iterator")
             * (@current_queue_list_size=2)
             * (@current_automaton_state="HasNextstart")
             * (@queue_event_1_position_1=_log_queue_1_1)
             * (@queue_event_0_position_1=_log_queue_0_1)
             * (@queue_event_1_position_0=_log_queue_1_0)
             * (@queue_event_0_position_0=_log_queue_0_0)
             * (_log_register_i_1_trans_1=_log_register_i_0))
         || ((@register_i=_log_register_i_0)
             * (@queue_event_0_position_0
               !="return_$$_java.util.Collection.iterator$$$$java.util.Iterator")
             * (@current_queue_list_size=2)
             * (@current_automaton_state="HasNextstart")
             * (@queue_event_1_position_1=_log_queue_1_1)
             * (@queue_event_0_position_1=_log_queue_0_1)
             * (@queue_event_1_position_0=_log_queue_1_0)
             * (@queue_event_0_position_0=_log_queue_0_0)
             * (@queue_event_0_position_0
               ="call_$$_java.util.Iterator.next$$$$java.lang.Object")
             * (_log_register_i_1_trans_1=_log_register_i_0)))}
      (@current_queue_list_size,@register_i,@current_queue_list_size
      ,@queue_event_0_position_1,@queue_event_0_position_0)
      {((@current_automaton_state="HasNextstart")
        * (@current_queue_list_size=1)
        * (@queue_event_0_position_1=_log_queue_1_1)
        * (@queue_event_0_position_0=_log_queue_1_0)
        * (@register_i=_log_register_i_1_trans_1))}
      +
      {((@register_i=_log_register_i_0)
         * (@queue_event_0_position_1=_log_queue_0_1)
         * (@current_automaton_state="HasNextinvalid")
         * (@queue_event_0_position_0=_log_queue_0_0)
         * (_log_register_i_1_trans_1=_log_register_i_0)
         * (@current_queue_list_size=2)
         * (@queue_event_0_position_1=_log_register_i_0)
         * (_log_register_i_1_trans_0=_log_register_i_0)
         * (@queue_event_1_position_0
           ="return_$$_java.util.Iterator.hasNext$$$$boolean")
         * (@queue_event_1_position_1=_log_queue_1_1)
         * (@queue_event_0_position_0
           ="call_$$_java.util.Iterator.hasNext$$$$boolean")
         * (@queue_event_1_position_0=_log_queue_1_0)
         * (_log_register_i_2_trans_1=_log_register_i_1_trans_1)
         * (@queue_event_0_position_0
           ="call_$$_java.util.Iterator.next$$$$java.lang.Object")
         * (@queue_event_1_position_1!=0))}
      (@current_queue_list_size,@current_automaton_state,@register_i
      ,@current_queue_list_size,@current_queue_list_size
      ,@current_automaton_state,@register_i,@current_queue_list_size
      ,@queue_event_0_position_1,@queue_event_0_position_0)
      {(((@register_i=_log_register_i_2_trans_1)
         * (@current_queue_list_size=0)
         * (@current_automaton_state="HasNextvalid"))
        || ((@current_queue_list_size=1)
            * (@queue_event_0_position_1=_log_queue_1_1)
            * (@queue_event_0_position_0=_log_queue_1_0)
            * (@current_automaton_state="HasNexterror")
            * (@register_i=_log_register_i_1_trans_0)))}
      +{((@current_automaton_state="HasNexterror")
         * (@queue_event_1_position_1=_log_queue_1_1)
         * (@register_i=_log_register_i_0)
         * (@queue_event_1_position_0=_log_queue_1_0)
         * (@queue_event_0_position_1=_log_queue_0_1)
         * (@current_queue_list_size=2)
         * (@queue_event_0_position_0=_log_queue_0_0))}
      (@current_queue_list_size,@queue_event_0_position_1
      ,@queue_event_0_position_0)
      {((@register_i=_log_register_i_0) * (@current_queue_list_size=1)
        * (@queue_event_0_position_1=_log_queue_1_1)
        * (@queue_event_0_position_0=_log_queue_1_0)
        * (@current_automaton_state="HasNexterror"))}
      +{(((@register_i=_log_register_i_0)
          * (@queue_event_0_position_1=_log_queue_0_1)
          * (@queue_event_0_position_0=_log_queue_0_0)
          * (@current_automaton_state="HasNextvalid")
          * (@queue_event_1_position_1=_log_queue_1_1)
          * (@queue_event_1_position_0=_log_queue_1_0)
          * (@queue_event_0_position_0
            !="call_$$_java.util.Iterator.next$$$$java.lang.Object")
          * (@current_queue_list_size=2))
         || ((@register_i=_log_register_i_0)
             * (@queue_event_0_position_1=_log_queue_0_1)
             * (@queue_event_0_position_0=_log_queue_0_0)
             * (@current_automaton_state="HasNextvalid")
             * (@queue_event_1_position_1=_log_queue_1_1)
             * (@queue_event_1_position_0=_log_queue_1_0)
             * (@queue_event_0_position_1!=_log_register_i_0)
             * (@current_queue_list_size=2)))}
      (@current_queue_list_size,@queue_event_0_position_1
      ,@queue_event_0_position_0)
      {((@register_i=_log_register_i_0) * (@current_queue_list_size=1)
        * (@queue_event_0_position_1=_log_queue_1_1)
        * (@queue_event_0_position_0=_log_queue_1_0)
        * (@current_automaton_state="HasNextvalid"))}
      +{((@current_queue_list_size=2)
         * (@queue_event_0_position_0
           !="call_$$_java.util.Collection.iterator$$$$java.util.Iterator")
         * (@queue_event_1_position_0=_log_queue_1_0)
         * (@current_automaton_state="HasNextstart")
         * (@queue_event_0_position_0
           !="return_$$_java.util.Collection.iterator$$$$java.util.Iterator")
         * (@queue_event_0_position_0=_log_queue_0_0)
         * (@queue_event_0_position_0
           !="call_$$_java.util.Iterator.hasNext$$$$boolean")
         * (@register_i=_log_register_i_0)
         * (@queue_event_1_position_1=_log_queue_1_1)
         * (@queue_event_0_position_0
           !="call_$$_java.util.Iterator.next$$$$java.lang.Object")
         * (@queue_event_0_position_1=_log_queue_0_1)
         * (@queue_event_0_position_0
           !="return_$$_java.util.Iterator.next$$$$java.lang.Object")
         * (@queue_event_0_position_0
           !="return_$$_java.util.Iterator.hasNext$$$$boolean"))}
      (@current_queue_list_size,@queue_event_0_position_1
      ,@queue_event_0_position_0)
      {((@current_automaton_state="HasNextstart")
        * (@register_i=_log_register_i_0) * (@current_queue_list_size=1)
        * (@queue_event_0_position_1=_log_queue_1_1)
        * (@queue_event_0_position_0=_log_queue_1_0))}
      +{(((@queue_event_0_position_0
          ="return_$$_java.util.Collection.iterator$$$$java.util.Iterator")
          * (_log_register_i_1_trans_1=_log_register_i_0)
          * (_log_register_i_1_trans_0=@queue_event_0_position_1)
          * (@register_i=_log_register_i_0)
          * (@current_queue_list_size=2)
          * (@queue_event_1_position_0=_log_queue_1_0)
          * (@queue_event_0_position_0
            ="call_$$_java.util.Iterator.hasNext$$$$boolean")
          * (@queue_event_0_position_0=_log_queue_0_0)
          * (@queue_event_1_position_1=_log_queue_1_1)
          * (@current_automaton_state="HasNextstart")
          * (@queue_event_0_position_1=_log_queue_0_1))
         || ((@queue_event_0_position_0
             ="return_$$_java.util.Collection.iterator$$$$java.util.Iterator")
             * (_log_register_i_1_trans_1=_log_register_i_0)
             * (_log_register_i_1_trans_0=@queue_event_0_position_1)
             * (@register_i=_log_register_i_0)
             * (@current_queue_list_size=2)
             * (@queue_event_1_position_0=_log_queue_1_0)
             * (@queue_event_0_position_0=_log_queue_0_0)
             * (@queue_event_1_position_1=_log_queue_1_1)
             * (@current_automaton_state="HasNextstart")
             * (@queue_event_0_position_1=_log_queue_0_1)
             * (@queue_event_0_position_0
               ="call_$$_java.util.Iterator.next$$$$java.lang.Object"))
         || ((@queue_event_0_position_0
             ="return_$$_java.util.Collection.iterator$$$$java.util.Iterator")
             * (_log_register_i_1_trans_1=_log_register_i_0)
             * (_log_register_i_1_trans_0=@queue_event_0_position_1)
             * (@register_i=_log_register_i_0)
             * (@current_queue_list_size=2)
             * (@queue_event_1_position_0=_log_queue_1_0)
             * (@queue_event_0_position_0
               ="return_$$_java.util.Iterator.next$$$$java.lang.Object")
             * (@queue_event_0_position_0=_log_queue_0_0)
             * (@queue_event_1_position_1=_log_queue_1_1)
             * (@current_automaton_state="HasNextstart")
             * (@queue_event_0_position_1=_log_queue_0_1))
         || ((@queue_event_0_position_0
             ="return_$$_java.util.Collection.iterator$$$$java.util.Iterator")
             * (_log_register_i_1_trans_1=_log_register_i_0)
             * (_log_register_i_1_trans_0=@queue_event_0_position_1)
             * (@register_i=_log_register_i_0)
             * (@current_queue_list_size=2)
             * (@queue_event_1_position_0=_log_queue_1_0)
             * (@queue_event_0_position_0
               ="call_$$_java.util.Collection.iterator$$$$java.util.Iterator")
             * (@queue_event_0_position_0=_log_queue_0_0)
             * (@queue_event_1_position_1=_log_queue_1_1)
             * (@current_automaton_state="HasNextstart")
             * (@queue_event_0_position_1=_log_queue_0_1))
         || ((@queue_event_0_position_0
             ="return_$$_java.util.Collection.iterator$$$$java.util.Iterator")
             * (_log_register_i_1_trans_1=_log_register_i_0)
             * (_log_register_i_1_trans_0=@queue_event_0_position_1)
             * (@register_i=_log_register_i_0)
             * (@current_queue_list_size=2)
             * (@queue_event_1_position_0=_log_queue_1_0)
             * (@queue_event_0_position_0=_log_queue_0_0)
             * (@queue_event_1_position_1=_log_queue_1_1)
             * (@current_automaton_state="HasNextstart")
             * (@queue_event_0_position_0
               ="return_$$_java.util.Iterator.hasNext$$$$boolean")
             * (@queue_event_0_position_1=_log_queue_0_1))
         || ((@queue_event_0_position_0
             ="return_$$_java.util.Collection.iterator$$$$java.util.Iterator")
             * (@register_i=_log_register_i_0)
             * (@current_queue_list_size=2)
             * (@current_automaton_state="HasNextstart")
             * (@queue_event_1_position_1=_log_queue_1_1)
             * (@queue_event_0_position_1=_log_queue_0_1)
             * (@queue_event_1_position_0=_log_queue_1_0)
             * (@queue_event_0_position_0=_log_queue_0_0)
             * (_log_register_i_1_trans_1=_log_register_i_0)
             * (_log_register_i_1_trans_0=@queue_event_0_position_1)))}
      (@current_queue_list_size,@register_i,@current_queue_list_size
      ,@queue_event_0_position_1,@queue_event_0_position_0
      ,@current_queue_list_size,@current_automaton_state,@register_i
      ,@current_queue_list_size,@queue_event_0_position_1
      ,@queue_event_0_position_0)
      {(((@current_automaton_state="HasNextstart")
         * (@current_queue_list_size=1)
         * (@queue_event_0_position_1=_log_queue_1_1)
         * (@queue_event_0_position_0=_log_queue_1_0)
         * (@register_i=_log_register_i_1_trans_1))
        || ((@current_queue_list_size=1)
            * (@queue_event_0_position_1=_log_queue_1_1)
            * (@current_automaton_state="HasNextinvalid")
            * (@queue_event_0_position_0=_log_queue_1_0)
            * (@register_i=_log_register_i_1_trans_0)))}
      +{((@register_i=_log_register_i_0)
         * (@queue_event_0_position_1=_log_queue_0_1)
         * (@queue_event_0_position_0
           !="return_$$_java.util.Collection.iterator$$$$java.util.Iterator")
         * (@queue_event_0_position_0=_log_queue_0_0)
         * (@current_queue_list_size=2)
         * (@queue_event_0_position_0
           !="call_$$_java.util.Iterator.next$$$$java.lang.Object")
         * (@queue_event_1_position_1=_log_queue_1_1)
         * (@queue_event_0_position_0
           !="return_$$_java.util.Iterator.hasNext$$$$boolean")
         * (@queue_event_1_position_0=_log_queue_1_0)
         * (_log_register_i_1_trans_0=@queue_event_0_position_1)
         * (@current_automaton_state="HasNextstart")
         * (@queue_event_0_position_0
           ="return_$$_java.util.Collection.iterator$$$$java.util.Iterator")
         * (@queue_event_0_position_0
           !="call_$$_java.util.Collection.iterator$$$$java.util.Iterator")
         * (@queue_event_0_position_0
           !="return_$$_java.util.Iterator.next$$$$java.lang.Object")
         * (@queue_event_0_position_0
           !="call_$$_java.util.Iterator.hasNext$$$$boolean"))}
      (@current_queue_list_size,@current_automaton_state,@register_i
      ,@current_queue_list_size,@queue_event_0_position_1
      ,@queue_event_0_position_0)
      {((@current_queue_list_size=1)
        * (@queue_event_0_position_1=_log_queue_1_1)
        * (@current_automaton_state="HasNextinvalid")
        * (@queue_event_0_position_0=_log_queue_1_0)
        * (@register_i=_log_register_i_1_trans_0))}
      +{(((@register_i=_log_register_i_0) * (@current_queue_list_size=2)
          * (@queue_event_1_position_0=_log_queue_1_0)
          * (_log_register_i_1_trans_0=_log_register_i_0)
          * (@queue_event_0_position_0
            !="call_$$_java.util.Iterator.hasNext$$$$boolean")
          * (@queue_event_0_position_0=_log_queue_0_0)
          * (@queue_event_1_position_1=_log_queue_1_1)
          * (@queue_event_0_position_1=_log_register_i_0)
          * (@current_automaton_state="HasNextinvalid")
          * (@queue_event_0_position_1=_log_queue_0_1)
          * (@queue_event_0_position_0
            ="call_$$_java.util.Iterator.next$$$$java.lang.Object"))
         || ((@register_i=_log_register_i_0)
             * (@queue_event_1_position_1=_log_queue_1_1)
             * (@current_automaton_state="HasNextinvalid")
             * (_log_register_i_1_trans_0=_log_register_i_0)
             * (@queue_event_0_position_0
               ="call_$$_java.util.Iterator.next$$$$java.lang.Object")
             * (@queue_event_1_position_0
               !="return_$$_java.util.Iterator.hasNext$$$$boolean")
             * (@queue_event_0_position_0=_log_queue_0_0)
             * (_log_register_i_1_trans_1=_log_register_i_0)
             * (@queue_event_1_position_0=_log_queue_1_0)
             * (@queue_event_0_position_1=_log_register_i_0)
             * (@current_queue_list_size=2)
             * (@queue_event_0_position_1=_log_queue_0_1))
         || ((@register_i=_log_register_i_0)
             * (@queue_event_1_position_1=_log_queue_1_1)
             * (@current_automaton_state="HasNextinvalid")
             * (_log_register_i_1_trans_0=_log_register_i_0)
             * (@queue_event_0_position_0
               ="call_$$_java.util.Iterator.next$$$$java.lang.Object")
             * (@queue_event_1_position_1=0)
             * (@queue_event_0_position_0=_log_queue_0_0)
             * (_log_register_i_1_trans_1=_log_register_i_0)
             * (@queue_event_1_position_0=_log_queue_1_0)
             * (@queue_event_0_position_1=_log_register_i_0)
             * (@current_queue_list_size=2)
             * (@queue_event_0_position_1=_log_queue_0_1))
         || ((@register_i=_log_register_i_0)
             * (@current_queue_list_size=2)
             * (@queue_event_1_position_0=_log_queue_1_0)
             * (_log_register_i_1_trans_0=_log_register_i_0)
             * (@queue_event_0_position_0=_log_queue_0_0)
             * (@queue_event_1_position_1=_log_queue_1_1)
             * (@queue_event_0_position_1=_log_register_i_0)
             * (@queue_event_0_position_1!=_log_register_i_0)
             * (@current_automaton_state="HasNextinvalid")
             * (@queue_event_0_position_1=_log_queue_0_1)
             * (@queue_event_0_position_0
               ="call_$$_java.util.Iterator.next$$$$java.lang.Object")))}
      (@current_queue_list_size,@current_automaton_state,@register_i
      ,@current_queue_list_size,@queue_event_0_position_1
      ,@queue_event_0_position_0)
      {((@current_queue_list_size=1)
        * (@queue_event_0_position_1=_log_queue_1_1)
        * (@queue_event_0_position_0=_log_queue_1_0)
        * (@current_automaton_state="HasNexterror")
        * (@register_i=_log_register_i_1_trans_0))}
      +{(((@queue_event_1_position_1!=0)
          * (@queue_event_1_position_1=_log_queue_1_1)
          * (@queue_event_0_position_1=_log_register_i_0)
          * (@current_automaton_state="HasNextinvalid")
          * (@queue_event_0_position_1=_log_queue_0_1)
          * (@queue_event_1_position_0
            ="return_$$_java.util.Iterator.hasNext$$$$boolean")
          * (@queue_event_0_position_0
            ="call_$$_java.util.Iterator.hasNext$$$$boolean")
          * (@register_i=_log_register_i_0)
          * (@queue_event_1_position_0=_log_queue_1_0)
          * (@queue_event_0_position_0
            !="call_$$_java.util.Iterator.next$$$$java.lang.Object")
          * (_log_register_i_1_trans_1=_log_register_i_0)
          * (@current_queue_list_size=2)
          * (@queue_event_0_position_0=_log_queue_0_0)
          * (_log_register_i_2_trans_1=_log_register_i_1_trans_1))
         || ((@queue_event_1_position_1!=0)
             * (@queue_event_1_position_1=_log_queue_1_1)
             * (@queue_event_0_position_1!=_log_register_i_0)
             * (@queue_event_0_position_1=_log_register_i_0)
             * (@current_automaton_state="HasNextinvalid")
             * (@queue_event_0_position_1=_log_queue_0_1)
             * (@queue_event_1_position_0
               ="return_$$_java.util.Iterator.hasNext$$$$boolean")
             * (@queue_event_0_position_0
               ="call_$$_java.util.Iterator.hasNext$$$$boolean")
             * (@register_i=_log_register_i_0)
             * (@queue_event_1_position_0=_log_queue_1_0)
             * (_log_register_i_1_trans_1=_log_register_i_0)
             * (@current_queue_list_size=2)
             * (@queue_event_0_position_0=_log_queue_0_0)
             * (_log_register_i_2_trans_1=_log_register_i_1_trans_1)))}
      (@current_queue_list_size,@current_automaton_state,@register_i
      ,@current_queue_list_size)
      {((@register_i=_log_register_i_2_trans_1)
        * (@current_queue_list_size=0)
        * (@current_automaton_state="HasNextvalid"))}
      +{((@register_i=_log_register_i_0)
         * (_log_register_i_1_trans_0=_log_register_i_0)
         * (@queue_event_0_position_1=_log_register_i_0)
         * (@current_queue_list_size=2)
         * (@queue_event_1_position_1=_log_queue_1_1)
         * (@queue_event_0_position_1=_log_queue_0_1)
         * (@queue_event_1_position_0=_log_queue_1_0)
         * (@queue_event_0_position_0=_log_queue_0_0)
         * (@queue_event_0_position_0
           ="call_$$_java.util.Iterator.next$$$$java.lang.Object")
         * (@current_automaton_state="HasNextvalid"))}
      (@current_queue_list_size,@current_automaton_state,@register_i
      ,@current_queue_list_size,@queue_event_0_position_1
      ,@queue_event_0_position_0)
      {((@current_queue_list_size=1)
        * (@queue_event_0_position_1=_log_queue_1_1)
        * (@current_automaton_state="HasNextinvalid")
        * (@queue_event_0_position_0=_log_queue_1_0)
        * (@register_i=_log_register_i_1_trans_0))}
    procedure enqueue_$$ 
      {(@current_queue_list_size=1)}
      (@current_queue_list_size,@queue_event_1_position_0
      ,@queue_event_1_position_1)
      {((@queue_event_1_position_1=@parameter1)
        * (@current_queue_list_size=2)
        * (@queue_event_1_position_0=@parameter0))}
      +{(@current_queue_list_size=0)}
      (@current_queue_list_size,@queue_event_0_position_0
      ,@queue_event_0_position_1)
      {((@queue_event_0_position_1=@parameter1)
        * (@current_queue_list_size=1)
        * (@queue_event_0_position_0=@parameter0))}


procedure java.util.ArrayList.ensureCapacity$$int$$void 
  
:
  call emit_$$("call_$$_java.util.ArrayList.ensureCapacity$$int$$void");
  call java.util.ArrayList.ensureCapacity$$int$$void_I();
  call 
    :=emit_$$("return_$$_java.util.ArrayList.ensureCapacity$$int$$void");

procedure java.util.ArrayList.ensureCapacity$$int$$void_I 
  
:
  assign r0:={emp}(){($ret_v0=@this)}();
  assign i0:={emp}(){($ret_v0=@parameter0)}();
  goto gen_7,gen_8;
  label gen_7;
  spec {emp}(){i0 <= 0};
  goto label0;
  label gen_8;
  spec {emp}(){i0 > 0};
  label label0;
  nop;

