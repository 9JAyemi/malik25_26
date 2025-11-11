// SVA for sm_timer_64
// Bind this file to the DUT: bind sm_timer_64 sm_timer_64_sva u_sva();

module sm_timer_64_sva();

  // Mirror encodings used by DUT
  localparam [7:0] Fetch      = 8'b00000001;
  localparam [7:0] Decode     = 8'b00000010;
  localparam [7:0] SMSEND_Lo  = 8'b01000000;
  localparam [7:0] SMSEND_Hi  = 8'b10000000;

  localparam [15:0] OPSTART   = 16'h0001;
  localparam [15:0] OPSTOP    = 16'h0002;
  localparam [15:0] OPRESET   = 16'h0003;
  localparam [15:0] OPREAD    = 16'h0004;

  // Default SVA context
  default clocking cb @(posedge ACLK); endclocking
  default disable iff (!ARESETN);

  // =========================================================================
  // Structural/encoding checks
  // =========================================================================
  // State must be one of the implemented states
  ap_state_legal: assert property (state inside {Fetch, Decode, SMSEND_Lo, SMSEND_Hi});

  // Interface encodings must match state
  ap_cmd_ready_eq_fetch: assert property (sCMD_tready == (state == Fetch));
  ap_mret_valid_eq_send: assert property (mRet_tvalid == (state == SMSEND_Lo || state == SMSEND_Hi));

  // mRet data always mirrors rVal
  ap_mret_data_eq_rval:  assert property (mRet_tdata == rVal);

  // =========================================================================
  // Command side: fetch/decode and instruction capture
  // =========================================================================
  // Fetch: advance to Decode only when valid; otherwise stay
  ap_fetch_to_decode: assert property ((state == Fetch && sCMD_tvalid) |=> state == Decode);
  ap_fetch_stay:      assert property ((state == Fetch && !sCMD_tvalid) |=> state == Fetch);

  // Instruction capture on fetch when valid
  ap_instr_capture:   assert property ((state == Fetch && sCMD_tvalid) |=> instruction == $past(sCMD_tdata));

  // Instruction must not change outside capture point
  ap_instr_stable_else: assert property (! (state == Fetch && sCMD_tvalid) |=> $stable(instruction));

  // =========================================================================
  // Decode actions
  // =========================================================================
  ap_dec_start:  assert property ((state == Decode && instruction[31:16] == OPSTART) |=> (state == Fetch && rEN));
  ap_dec_stop:   assert property ((state == Decode && instruction[31:16] == OPSTOP ) |=> (state == Fetch && !rEN));
  ap_dec_reset:  assert property ((state == Decode && instruction[31:16] == OPRESET) |=> (state == Fetch && rRESET));
  ap_dec_read:   assert property ((state == Decode && instruction[31:16] == OPREAD ) |=> (state == SMSEND_Lo && rVal == $past(counterR[31:0])));

  // Default decode returns to Fetch
  ap_dec_default_to_fetch: assert property ((state == Decode &&
                                            !(instruction[31:16] inside {OPSTART,OPSTOP,OPRESET,OPREAD}))
                                            |=> state == Fetch);

  // Control signal change provenance
  ap_ren_changes_only_on_start_stop: assert property ($changed(rEN) |-> ($past(state) == Decode &&
                                                                        ($past(instruction[31:16]) inside {OPSTART,OPSTOP})));
  ap_rreset_rise_only_on_opreset:    assert property ($rose(rRESET) |-> ($past(state) == Decode &&
                                                                        $past(instruction[31:16]) == OPRESET));
  ap_rreset_falls_in_fetch:          assert property ($fell(rRESET) |-> $past(state) == Fetch);

  // =========================================================================
  // Return channel behavior (two-beat read)
  // =========================================================================
  // Entering SMSEND_Lo only comes from OPREAD
  ap_sendlo_origin: assert property ((state == SMSEND_Lo) |-> ($past(state) == Decode &&
                                                               $past(instruction[31:16]) == OPREAD));

  // SMSEND_Lo: on handshake, advance and update rVal with high word snapshot; else hold state/data
  ap_lo_advance:  assert property ((state == SMSEND_Lo && mRet_tready) |=> (state == SMSEND_Hi &&
                                                                             rVal == $past(counterR[63:32])));
  ap_lo_hold:     assert property ((state == SMSEND_Lo && !mRet_tready) |=> (state == SMSEND_Lo &&
                                                                              $stable(rVal)));

  // SMSEND_Hi: on handshake, return to Fetch; else hold state/data
  ap_hi_advance:  assert property ((state == SMSEND_Hi && mRet_tready) |=> state == Fetch);
  ap_hi_hold:     assert property ((state == SMSEND_Hi && !mRet_tready) |=> (state == SMSEND_Hi &&
                                                                              $stable(rVal)));

  // Full two-beat transaction completes before next Fetch
  ap_two_beat_read: assert property (
    (state == Decode && instruction[31:16] == OPREAD)
      ##1 (state == SMSEND_Lo)
      ##[1:$] (state == SMSEND_Lo && mRet_tready)
      ##1 (state == SMSEND_Hi)
      ##[1:$] (state == SMSEND_Hi && mRet_tready)
      ##1 (state == Fetch)
  );

  // =========================================================================
  // Counter behavior
  // =========================================================================
  // Reset behavior
  ap_counter_zero_on_rreset: assert property (rRESET |=> counterR == 64'd0);

  // Increment/hold behavior when not resetting
  ap_counter_inc:  assert property ((!rRESET && rEN)  |=> counterR == $past(counterR) + 64'd1);
  ap_counter_hold: assert property ((!rRESET && !rEN) |=> counterR == $past(counterR));

  // =========================================================================
  // Covers
  // =========================================================================
  // Cover OPSTART then counter increments then OPSTOP
  cv_start_stop: cover property (
    (state == Decode && instruction[31:16] == OPSTART)
      ##1 (state == Fetch && rEN)
      ##[2:5] (!rRESET && rEN)
      ##1 (state == Decode && instruction[31:16] == OPSTOP)
      ##1 (!rEN)
  );

  // Cover OPRESET pulse behavior (assert then deassert in Fetch)
  cv_opreset_pulse: cover property (
    (state == Decode && instruction[31:16] == OPRESET)
      ##1 (state == Fetch && rRESET)
      ##1 (!rRESET)
  );

  // Cover a read with backpressure on first beat only
  cv_read_bp_lo: cover property (
    (state == Decode && instruction[31:16] == OPREAD)
      ##1 (state == SMSEND_Lo && !mRet_tready)[*2:$]
      ##1 (state == SMSEND_Lo && mRet_tready)
      ##1 (state == SMSEND_Hi && mRet_tready)
      ##1 (state == Fetch)
  );

  // Cover a read with backpressure on second beat only
  cv_read_bp_hi: cover property (
    (state == Decode && instruction[31:16] == OPREAD)
      ##1 (state == SMSEND_Lo && mRet_tready)
      ##1 (state == SMSEND_Hi && !mRet_tready)[*2:$]
      ##1 (state == SMSEND_Hi && mRet_tready)
      ##1 (state == Fetch)
  );

endmodule

bind sm_timer_64 sm_timer_64_sva u_sm_timer_64_sva();