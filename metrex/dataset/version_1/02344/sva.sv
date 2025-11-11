// SVA for uart_tx — bindable, concise, and focused on functional checks and coverage
module uart_tx_sva #(parameter int DBIT = 8, SB_TICK = 16) ();

  // Mirror DUT encodings for readability
  localparam [1:0] IDLE=2'b00, START=2'b01, DATA=2'b10, STOP=2'b11;

  // This module is bound inside uart_tx, so these names resolve in that scope:
  // clk, reset, s_tick, tx_start, data_in, tx_done_tick, data_out
  // state_reg, cnt_15_reg, cnt_8_reg, shift_out_reg, tx_reg

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Static parameter sanity (catches design mismatches)
  initial begin
    if (DBIT < 1 || DBIT > 8) $error("uart_tx: DBIT (%0d) must be 1..8", DBIT);
    if ($clog2(SB_TICK) > $bits(cnt_15_reg))
      $error("uart_tx: SB_TICK (%0d) does not fit cnt_15_reg width (%0d)", SB_TICK, $bits(cnt_15_reg));
  end

  // Basic invariants
  a_tx_mux:            assert property (data_out == tx_reg);
  a_idle_high:         assert property (state_reg==IDLE  |-> data_out==1);
  a_start_low:         assert property (state_reg==START |-> data_out==0);
  a_data_drive_lsb:    assert property (state_reg==DATA  |-> data_out==shift_out_reg[0]);
  a_stop_high:         assert property (state_reg==STOP  |-> data_out==1);

  // Idle behavior
  a_idle_stable_no_start: assert property (state_reg==IDLE && !tx_start |=> state_reg==IDLE && $stable({cnt_15_reg,cnt_8_reg,shift_out_reg}));
  a_start_entry_load:     assert property (state_reg==IDLE && tx_start |=> state_reg==START && cnt_15_reg==0 && shift_out_reg==$past(data_in));

  // START timing
  a_start_no_tick_hold:   assert property (state_reg==START && !s_tick |=> state_reg==START && cnt_15_reg==$past(cnt_15_reg));
  a_start_tick_incr:      assert property (state_reg==START && s_tick && cnt_15_reg!=15 |=> state_reg==START && cnt_15_reg==$past(cnt_15_reg)+1);
  a_start_to_data:        assert property (state_reg==START && s_tick && cnt_15_reg==15 |=> state_reg==DATA && cnt_15_reg==0 && cnt_8_reg==0);

  // DATA timing and shifting
  a_data_no_tick_hold:    assert property (state_reg==DATA && !s_tick |=> $stable({cnt_15_reg,cnt_8_reg,shift_out_reg}));
  a_data_tick_incr:       assert property (state_reg==DATA && s_tick && cnt_15_reg!=15 |=> state_reg==DATA && cnt_15_reg==$past(cnt_15_reg)+1 && cnt_8_reg==$past(cnt_8_reg));
  a_data_bit_boundary_not_last:
                          assert property (state_reg==DATA && s_tick && cnt_15_reg==15 && cnt_8_reg != (DBIT-1)
                                           |=> state_reg==DATA && cnt_15_reg==0 && cnt_8_reg==$past(cnt_8_reg)+1 && shift_out_reg==$past(shift_out_reg)>>1);
  // Require transition to STOP after last data bit (exposes SB_TICK != 16 bug in DUT)
  a_data_last_to_stop:    assert property (state_reg==DATA && s_tick && cnt_15_reg==15 && cnt_8_reg == (DBIT-1)
                                           |=> state_reg==STOP && cnt_15_reg==0);

  // STOP timing and done pulse
  a_stop_no_tick_hold:    assert property (state_reg==STOP && !s_tick |=> state_reg==STOP && cnt_15_reg==$past(cnt_15_reg) && !tx_done_tick);
  a_stop_tick_incr:       assert property (state_reg==STOP && s_tick && cnt_15_reg != (SB_TICK-1)
                                           |=> state_reg==STOP && cnt_15_reg==$past(cnt_15_reg)+1 && !tx_done_tick);
  a_stop_to_idle:         assert property (state_reg==STOP && s_tick && cnt_15_reg == (SB_TICK-1) |=> state_reg==IDLE);
  a_done_pulse_where:     assert property (tx_done_tick |-> state_reg==STOP && s_tick && cnt_15_reg==(SB_TICK-1));
  a_done_one_cycle:       assert property ($rose(tx_done_tick) |=> !tx_done_tick);

  // Coverage: a complete frame (start->data->stop with done)
  c_full_frame: cover property (
    state_reg==IDLE && tx_start
    ##1 state_reg==START
    ##[1:$] (state_reg==DATA)
    ##[1:$] (state_reg==STOP && s_tick && cnt_15_reg==(SB_TICK-1) && tx_done_tick)
    ##1 state_reg==IDLE
  );

endmodule

bind uart_tx uart_tx_sva #(.DBIT(DBIT), .SB_TICK(SB_TICK)) u_uart_tx_sva();