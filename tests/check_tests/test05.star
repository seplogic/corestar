global state;

procedure test05:
{
   (_$g_current_queue_list_size_2 = "0") *
   ($g_current_queue_list_size = _$g_current_queue_list_size_2) * 
   (_parameter0_4 != "return_$$_java.util.Iterator.next$$$$java.lang.Object") * 
   ($g_current_automaton_state = _$g_current_automaton_state_2)*
   (_$g_current_automaton_state_2 = "simplestart")* 
   (_parameter0_4
 !=     "call_$$_java.util.Iterator.next$$$$java.lang.Object")* 
   (_parameter0_4 = _log_queue_0_0_11) * 
   (@parameter0: = _parameter0_4)* 
   ($g_queue_event_0_position_0 = _$g_queue_event_0_position_0_2)* 
   (_parameter0_4 = _log_queue_0_0_21)
}
( $g_current_automaton_state
, $g_current_queue_list_size
, $g_queue_event_0_position_0 )
{
   ($g_queue_event_0_position_0
 !=     "return_$$_java.util.Iterator.next$$$$java.lang.Object") *
   ($g_queue_event_0_position_0 = _parameter0_4) *
   ($g_current_automaton_state = "simplestart") *
   ($g_queue_event_0_position_0
 !=     "call_$$_java.util.Iterator.next$$$$java.lang.Object") *
   ($g_current_automaton_state = _$g_current_automaton_state_2) *
   (_$g_current_queue_list_size_2 = $g_current_queue_list_size) *
   ($g_queue_event_0_position_0 = _log_queue_0_0_11) *
   ($g_queue_event_0_position_0 = _log_queue_0_0_21) *
   (@parameter0: = _parameter0_4) *
   ($g_current_automaton_state != "simpleerror") *
   ($g_current_queue_list_size = "0")
}
?
 assign
  {
   (_$g_current_queue_list_size_1 = "0") *
   ($g_current_queue_list_size = _$g_current_queue_list_size_1) *
   (_parameter0_3
 !=     "return_$$_java.util.Iterator.next$$$$java.lang.Object") *
   ($g_current_automaton_state = _$g_current_automaton_state_1) *
   (_$g_current_automaton_state_1 = "simplestart") *
   (_parameter0_3
 !=     "call_$$_java.util.Iterator.next$$$$java.lang.Object") *
   (_parameter0_3 = _log_queue_0_0_1) *
   (@parameter0: = _parameter0_3) *
   ($g_queue_event_0_position_0 = _$g_queue_event_0_position_0_1) *
   (_parameter0_3 = _log_queue_0_0_6)
  }
  ($g_current_automaton_state,$g_current_queue_list_size,$g_queue_event_0_position_0)
  {
   ($g_queue_event_0_position_0
 !=     "return_$$_java.util.Iterator.next$$$$java.lang.Object") *
   ($g_queue_event_0_position_0 = _parameter0_3) *
   ($g_current_automaton_state = "simplestart") *
   ($g_queue_event_0_position_0
 !=     "call_$$_java.util.Iterator.next$$$$java.lang.Object") *
   ($g_current_automaton_state = _$g_current_automaton_state_1) *
   (_$g_current_queue_list_size_1 = $g_current_queue_list_size) *
   ($g_queue_event_0_position_0 = _log_queue_0_0_1) *
   ($g_queue_event_0_position_0 = _log_queue_0_0_6) *
   (@parameter0: = _parameter0_3) *
   ($g_current_automaton_state != "simpleerror") *
   ($g_current_queue_list_size = "0")} ();
end;
