// SVA checker for signal_gen
// Bind example: bind signal_gen signal_gen_sva sv_chk();

module signal_gen_sva;

  default clocking cb @(posedge clk); endclocking

  // Basic sanity and encodings
  default disable iff (rst);
  a_no_x_outputs:        assert property (!$isunknown({stm_value, rsb, gnt})); 
  a_state_onehot:        assert property ($onehot(state));
  a_stm_alias:           assert property (stm_value == symb_value);
  a_rsb_alias:           assert property (rsb == rsb_int);

  // Reset value checks (synchronous)
  default disable iff (1'b0);
  a_reset_vals:          assert property (rst |=> state==IDLE && prev_cnt==0 && curr_cnt==0 && next_cnt==0
                                           && symb_value=={INPUT_PORTS{1'b0}} && gnt==1'b0);
  generate
    if ((RESET_PORT==1) && (RESET_SENS==0)) begin
      a_reset_rsb_ah:    assert property (rst |=> rsb_int==1'b0);
    end else begin
      a_reset_rsb_al:    assert property (rst |=> rsb_int==1'b1);
    end
  endgenerate

  // After reset, all other assertions enabled
  default disable iff (rst);

  // Legal state transitions
  a_idle_hold:           assert property (state==IDLE && !req |=> state==IDLE && gnt==0);
  a_idle_to_prev:        assert property (state==IDLE &&  req |=> state==PREV);

  a_prev_to_curr:        assert property (state==PREV && (prev_cnt < PREV_MAX || ((RESET_PORT==1) && (rst_invert==0))) |=> state==CURR);
  a_prev_to_idle:        assert property (state==PREV && (prev_cnt >= PREV_MAX) && (((RESET_PORT!=1)) || (rst_invert==1)) |=> state==IDLE);

  a_curr_to_next:        assert property (state==CURR |=> state==NEXT);
  a_next_to_prev:        assert property (state==NEXT |=> state==PREV);

  // Counter ranges
  a_rng_next:            assert property (next_cnt inside {[0:CNT_MAX-1]});
  a_rng_curr:            assert property (curr_cnt inside {[0:CNT_MAX-1]});
  a_rng_prev:            assert property (prev_cnt inside {[0:PREV_MAX]});

  // Counter progressions in NEXT
  a_next_incr:           assert property (state==NEXT && next_cnt < (CNT_MAX-1) |=> next_cnt == $past(next_cnt)+1);
  a_next_wrap:           assert property (state==NEXT && next_cnt == (CNT_MAX-1) |=> next_cnt == 0);

  a_curr_step:           assert property (state==NEXT && $past(next_cnt)==(CNT_MAX-1) && $past(curr_cnt)<(CNT_MAX-1)
                                          |=> curr_cnt == $past(curr_cnt)+1);
  a_curr_wrap:           assert property (state==NEXT && $past(next_cnt)==(CNT_MAX-1) && $past(curr_cnt)==(CNT_MAX-1)
                                          |=> curr_cnt == 0);

  a_prev_step:           assert property (state==NEXT && $past(next_cnt)==(CNT_MAX-1) && $past(curr_cnt)==(CNT_MAX-1)
                                          && $past(prev_cnt)<PREV_MAX
                                          |=> prev_cnt == $past(prev_cnt)+1);
  a_prev_wrap:           assert property (state==NEXT && $past(next_cnt)==(CNT_MAX-1) && $past(curr_cnt)==(CNT_MAX-1)
                                          && $past(prev_cnt)>=PREV_MAX
                                          |=> prev_cnt == 0);

  // symb_value mapping per state
  a_symb_curr:           assert property (state==CURR |-> stm_value == curr_cnt[INPUT_PORTS-1:0]);
  a_symb_next:           assert property (state==NEXT |-> stm_value == next_cnt[INPUT_PORTS-1:0]);
  a_symb_prev_lo:        assert property (state==PREV && (prev_cnt < PREV_HALF) |-> stm_value == {INPUT_PORTS{1'b0}});
  a_symb_prev_mid:       assert property (state==PREV && (prev_cnt >= PREV_HALF) && (prev_cnt < PREV_MAX) |-> stm_value == {INPUT_PORTS{1'b1}});
  a_symb_prev_hi:        assert property (state==PREV && (prev_cnt >= PREV_MAX) |-> stm_value == {INPUT_PORTS{1'b0}});

  // gnt behavior: only asserted at PREV terminal and leads to IDLE
  a_gnt_when:            assert property (gnt |-> state==PREV && prev_cnt>=PREV_MAX);
  a_gnt_to_idle:         assert property (gnt |=> state==IDLE);

  // rsb_int behavior around transaction start and PREV terminal
  generate
    if ((RESET_PORT==1) && (RESET_SENS==0)) begin : gen_rsb_ah
      a_idle_set_rsb:    assert property (state==IDLE && req |=> rsb_int==1'b0);
      a_prev_term_phase1:assert property (state==PREV && prev_cnt>=PREV_MAX && rst_invert==0
                                          |=> rsb_int==1'b1 && rst_invert==1'b1 && prev_cnt==0 && state==CURR);
      a_prev_term_phase2:assert property (state==PREV && prev_cnt>=PREV_MAX && rst_invert==1
                                          |=> rsb_int==1'b0 && gnt==1'b1 && rst_invert==1'b0 && state==IDLE);
    end else if ((RESET_PORT==1) && (RESET_SENS==1)) begin : gen_rsb_al
      a_idle_set_rsb:    assert property (state==IDLE && req |=> rsb_int==1'b1);
      a_prev_term_phase1:assert property (state==PREV && prev_cnt>=PREV_MAX && rst_invert==0
                                          |=> rsb_int==1'b0 && rst_invert==1'b1 && prev_cnt==0 && state==CURR);
      a_prev_term_phase2:assert property (state==PREV && prev_cnt>=PREV_MAX && rst_invert==1
                                          |=> rsb_int==1'b1 && gnt==1'b1 && rst_invert==1'b0 && state==IDLE);
    end else begin : gen_no_reset_port
      a_idle_set_rsb:    assert property (state==IDLE && req |=> rsb_int==1'b1);
      a_prev_term:       assert property (state==PREV && prev_cnt>=PREV_MAX
                                          |=> rsb_int==1'b0 && gnt==1'b1 && state==IDLE);
    end
  endgenerate

  // Functional coverage (concise, key milestones)
  c_state_cycle:         cover property (state==IDLE && req ##1 state==PREV ##1 state==CURR ##1 state==NEXT ##1 state==PREV);
  c_next_wrap:           cover property (state==NEXT && next_cnt==(CNT_MAX-1) ##1 state==PREV);
  c_curr_wrap:           cover property (state==NEXT && next_cnt==(CNT_MAX-1) && curr_cnt==(CNT_MAX-1));
  c_prev_wrap:           cover property (state==NEXT && next_cnt==(CNT_MAX-1) && curr_cnt==(CNT_MAX-1) && prev_cnt==PREV_MAX);
  c_gnt:                 cover property (gnt);

endmodule