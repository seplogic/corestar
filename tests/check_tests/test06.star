global state;


procedure test06:
{
   (_parameter0_4 != "call_next") *
   (_parameter0_4 = _log_queue_0_0_11) * 
   (@parameter0: = _parameter0_4) * 
   ($g_queue_event_0_position_0 = _$g_queue_event_0_position_0_2) * 
}
( $g_queue_event_0_position_0 )
{
   ($g_queue_event_0_position_0 = _parameter0_4) *
   ($g_queue_event_0_position_0 != "call_next") *
   ($g_queue_event_0_position_0 = _log_queue_0_0_11) *
   (@parameter0: = _parameter0_4)
}
?
 assign
  {
   (_parameter0_3 != "call_next") *
   (_parameter0_3 = _log_queue_0_0_1) *
   (@parameter0: = _parameter0_3) *
   ($g_queue_event_0_position_0 = _$g_queue_event_0_position_0_1) *
  }
  ( $g_queue_event_0_position_0 )
  {
   ($g_queue_event_0_position_0 = _parameter0_3) *
   ($g_queue_event_0_position_0 != "call_next") *
   ($g_queue_event_0_position_0 = _log_queue_0_0_1) *
   (@parameter0: = _parameter0_3) } ();
end;
