// SVA for UART_Sender
// Bind-in module uses internal signals; focuses on correctness and concise coverage

module UART_Sender_sva;
  default clocking cb @(posedge Clk); endclocking
  default disable iff (tReset);

  // Reset behavior and synchronizers
  a_reset_values:    assert property ( tReset |=> (Busy==0 && Tx==1 && State==Idle && Count==0 && BitCount==0) );
  a_treset_delay:    assert property ( $past(1'b1) |-> (tReset == $past(Reset)) );
  a_tsend_delay:     assert property ( $past(!tReset) |-> (tSend == $past(Send)) );

  // Count behavior
  a_count_dec:       assert property ( $past(!tReset) && $past(Count)!=0 |-> Count == $past(Count)-1 );
  a_reload_idle_ns:  assert property ( $past(Count)==0 && $past(State)==Idle    && !$past(tSend) |-> Count==0 );
  a_reload_idle_s:   assert property ( $past(Count)==0 && $past(State)==Idle    &&  $past(tSend) |-> Count==Full );
  a_reload_send:     assert property ( $past(Count)==0 && $past(State)==Sending                   |-> Count==Full );
  a_reload_stop:     assert property ( $past(Count)==0 && $past(State)==StopBit                   |-> Count==Full );
  a_reload_done:     assert property ( $past(Count)==0 && $past(State)==Done                      |-> Count==0 );

  // Busy invariants and edges
  a_busy_idle:       assert property ( State==Idle |-> !Busy );
  a_busy_nonidle:    assert property ( (State==Sending || State==StopBit || State==Done) |-> Busy );
  a_busy_tick_only:  assert property ( $changed(Busy) |-> $past(Count)==0 );

  // Tx behavior
  a_tx_idle_high:    assert property ( State==Idle |-> Tx==1 );
  a_tx_tick_only:    assert property ( $changed(Tx) |-> $past(Count)==0 );

  // BitCount sequencing
  a_bcnt_step:       assert property ( $past(Count)==0 && $past(State)==Sending |-> BitCount == $past(BitCount)-1 );
  a_bcnt_stable_nt:  assert property ( $past(Count)!=0 |-> BitCount == $past(BitCount) );

  // Shift/output correctness at bit boundaries
  a_start_load:      assert property ( $past(Count)==0 && $past(State)==Idle && $past(tSend)
                                       |-> Busy && Tx==0 && Temp==$past(Data) && BitCount==3'd7
                                           && State==Sending && Count==Full );
  a_tx_from_temp:    assert property ( $past(Count)==0 && $past(State)==Sending |-> Tx == $past(Temp[0]) );
  a_send_to_stop:    assert property ( $past(Count)==0 && $past(State)==Sending && $past(BitCount)==0
                                       |-> State==StopBit && Count==Full );
  a_stop_to_done:    assert property ( $past(Count)==0 && $past(State)==StopBit
                                       |-> Tx==1 && State==Done && Count==Full );
  a_done_hold_high:  assert property ( $past(Count)==0 && $past(State)==Done && $past(tSend)
                                       |-> Busy && State==Done && Count==0 );
  a_done_to_idle:    assert property ( $past(Count)==0 && $past(State)==Done && !$past(tSend)
                                       |-> !Busy && State==Idle && Count==0 );

  // Coverage
  sequence tick; ~|Count; endsequence

  c_start:           cover property ( tick && State==Idle && tSend );
  c_idle_no_send:    cover property ( tick && State==Idle && !tSend );
  c_states_path:     cover property ( tick ##[1:$] (State==Sending)
                                      ##[1:$] (State==StopBit)
                                      ##[1:$] (State==Done) );
  c_hold_in_done:    cover property ( (tick && State==Done && tSend)
                                      ##[1:$] (tick && State==Done && tSend) );

endmodule

bind UART_Sender UART_Sender_sva sva();