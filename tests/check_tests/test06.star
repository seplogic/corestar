procedure test06(%x)
  {
    _parameter0_3 != "call_next" *
    _parameter0_3 = _log_queue_0_0_1 *
    %x = _parameter0_3 *
    @queue_event_0_position_0 = _queue_event_0_position_0_1
  }
  ( @queue_event_0_position_0 )
  {
    @queue_event_0_position_0 = _parameter0_3 *
    @queue_event_0_position_0 != "call_next" *
    @queue_event_0_position_0 = _log_queue_0_0_1 *
    %x = _parameter0_3
  }
:
  spec
    {
      _parameter0_3 != "call_next" *
      _parameter0_3 = _log_queue_0_0_1 *
      %x = _parameter0_3 *
      @queue_event_0_position_0 = _queue_event_0_position_0_1
    }
    ( @queue_event_0_position_0 )
    {
      @queue_event_0_position_0 = _parameter0_3 *
      @queue_event_0_position_0 != "call_next" *
      @queue_event_0_position_0 = _log_queue_0_0_1 *
      %x = _parameter0_3
    }
  ;
