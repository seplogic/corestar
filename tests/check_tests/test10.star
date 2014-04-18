global @state;


procedure test10(%x):
{
   (_parameter0_4 != "call_next") *
   (_parameter0_4 = _log_queue_0_0_11) * 
   (%x = _parameter0_4) * 
   (@queue_event_0_position_0 = _queue_event_0_position_0_2)
}{} [%x]
?
 assign
  {
   (_parameter0_3 != "call_next") *
   (_parameter0_3 = _log_queue_0_0_1) *
   (%x = _parameter0_3) *
   (@queue_event_0_position_0 = _queue_event_0_position_0_1)
  }{} [%x] (%x);
end;
