
procedure test05:
{
   (_current_queue_list_size_2 = "0") *
   (@current_queue_list_size = _current_queue_list_size_2) * 
   (_parameter0_4 != "return_$$_java.util.Iterator.next$$$$java.lang.Object") *
   (@current_automaton_state = _current_automaton_state_2) *
   (_current_automaton_state_2 = "simplestart") * 
   (_parameter0_4 != "call_$$_java.util.Iterator.next$$$$java.lang.Object") * 
   (_parameter0_4 = _log_queue_0_0_11) * 
   (@parameter0 = _parameter0_4) * 
   (@queue_event_0_position_0 = _queue_event_0_position_0_2) * 
   (_parameter0_4 = _log_queue_0_0_21)
}
( @current_automaton_state
, @current_queue_list_size
, @queue_event_0_position_0 )
{
   (@queue_event_0_position_0 != "return_$$_java.util.Iterator.next$$$$java.lang.Object") *
   (@queue_event_0_position_0 = _parameter0_4) *
   (@current_automaton_state = "simplestart") *
   (@queue_event_0_position_0 != "call_$$_java.util.Iterator.next$$$$java.lang.Object") *
   (@current_automaton_state = _current_automaton_state_2) *
   (_current_queue_list_size_2 = @current_queue_list_size) *
   (@queue_event_0_position_0 = _log_queue_0_0_11) *
   (@queue_event_0_position_0 = _log_queue_0_0_21) *
   (@parameter0 = _parameter0_4) *
   (@current_automaton_state != "simpleerror") *
   (@current_queue_list_size = "0")
}
?
 assign
  {
   (_current_queue_list_size_1 = "0") *
   (@current_queue_list_size = _current_queue_list_size_1) *
   (_parameter0_3 != "return_$$_java.util.Iterator.next$$$$java.lang.Object") *
   (@current_automaton_state = _current_automaton_state_1) *
   (_current_automaton_state_1 = "simplestart") *
   (_parameter0_3 != "call_$$_java.util.Iterator.next$$$$java.lang.Object") *
   (_parameter0_3 = _log_queue_0_0_1) *
   (@parameter0 = _parameter0_3) *
   (@queue_event_0_position_0 = _queue_event_0_position_0_1) *
   (_parameter0_3 = _log_queue_0_0_6)
  }
  ( @current_automaton_state
  , @current_queue_list_size
  , @queue_event_0_position_0 )
  {
   (@queue_event_0_position_0 != "return_$$_java.util.Iterator.next$$$$java.lang.Object") *
   (@queue_event_0_position_0 = _parameter0_3) *
   (@current_automaton_state = "simplestart") *
   (@queue_event_0_position_0 != "call_$$_java.util.Iterator.next$$$$java.lang.Object") *
   (@current_automaton_state = _current_automaton_state_1) *
   (_current_queue_list_size_1 = @current_queue_list_size) *
   (@queue_event_0_position_0 = _log_queue_0_0_1) *
   (@queue_event_0_position_0 = _log_queue_0_0_6) *
   (@parameter0 = _parameter0_3) *
   (@current_automaton_state != "simpleerror") *
   (@current_queue_list_size = "0")} ();
end;
