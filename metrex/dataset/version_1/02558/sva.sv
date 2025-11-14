// SVA for ch_pcma: concise, high-quality checks and coverage
module ch_pcma_sva;
  // Bind into DUT’s scope
  default clocking cb @(posedge CLK); endclocking
  default disable iff (!nRESET)

  // Helpers
  let STOP_EQ   = (ADDR_CNT[19:8] == ADDR_STOP[11:0]);
  let SAMPLE_ACT = (RUN && CLK_SAMP && !STOP_EQ);

  // Static mapping
  a_rom_addr_map: assert property (ROM_ADDR == {ROM_BANK, ADDR_CNT});

  // Reset effects on key state regs
  a_reset_clear_core: assert property (!nRESET |-> (!RUN && !SET_FLAG && !PREV_FLAGMASK));

  // KEYON/KEYOFF behavior
  a_keyon_loads: assert property (
    (KEYON && !KEYOFF) |=> (RUN && 
                            (ADDR_CNT == {ADDR_START[11:0],8'h0}) &&
                            (ROM_BANK == ADDR_START[13:12]) &&
                            (END_FLAG == 1'b0) &&
                            (NIBBLE == 1'b0) &&
                            (ADPCM_ACC == 12'd0) &&
                            (ADPCM_STEP == 10'd0))
  );
  a_keyoff_run0: assert property (KEYOFF |=> !RUN);
  a_run_hold:    assert property ((!KEYON && !KEYOFF) |=> (RUN == $past(RUN)));

  // PREV_FLAGMASK tracking and END_FLAG clear on FLAGMASK rise
  a_prev_flagmask_update: assert property ((RUN && CLK_SAMP) |=> PREV_FLAGMASK == $past(FLAGMASK));
  a_endflag_clear_on_mask_rise: assert property ((RUN && CLK_SAMP && FLAGMASK && !PREV_FLAGMASK) |=> END_FLAG == 1'b0);

  // Stop condition handling
  a_stop_first_sets_flag: assert property ((RUN && CLK_SAMP && STOP_EQ && !SET_FLAG) |=> (SET_FLAG && (END_FLAG == ~ $past(FLAGMASK))));
  a_hold_while_stopped_cnt_nib: assert property ((RUN && CLK_SAMP && STOP_EQ) |=> (ADDR_CNT == $past(ADDR_CNT) && NIBBLE == $past(NIBBLE)));
  a_hold_while_stopped_state:   assert property ((RUN && CLK_SAMP && STOP_EQ) |=> (ADPCM_ACC == $past(ADPCM_ACC) && ADPCM_STEP == $past(ADPCM_STEP) && DATA == $past(DATA)));

  // Active sample path (non-stop): DATA mux, address inc, nibble toggle, accumulator, sample_out sign-ext
  a_data_hi_nibble: assert property ((SAMPLE_ACT && !NIBBLE) |=> (DATA == $past(ROM_DATA[7:4]) && ADDR_CNT == $past(ADDR_CNT)));
  a_data_lo_nibble: assert property ((SAMPLE_ACT &&  NIBBLE) |=> (DATA == $past(ROM_DATA[3:0]) && ADDR_CNT == $past(ADDR_CNT)+20'd1));
  a_nibble_toggle:  assert property (SAMPLE_ACT |=> NIBBLE == ~$past(NIBBLE));
  a_accum_update:   assert property (SAMPLE_ACT |=> ADPCM_ACC == $past(ADPCM_ACC) + $past(JEDI_DOUT));
  a_sample_out_se:  assert property (SAMPLE_ACT |=> (SAMPLE_OUT[11:0] == ADPCM_ACC && SAMPLE_OUT[15:12] == {4{ADPCM_ACC[11]}}));

  // ADPCM_STEP update rules and range
  a_step_range: assert property (ADPCM_STEP <= 10'd768);

  a_step_dec: assert property (
    (SAMPLE_ACT && (DATA[2:0] inside {3'd0,3'd1,3'd2,3'd3})) |=> 
      ADPCM_STEP == (($past(ADPCM_STEP) >= 10'd16) ? $past(ADPCM_STEP)-10'd16 : 10'd0)
  );
  a_step_inc32: assert property (
    (SAMPLE_ACT && (DATA[2:0] == 3'd4)) |=> 
      ADPCM_STEP == (($past(ADPCM_STEP) <= 10'd736) ? $past(ADPCM_STEP)+10'd32 : 10'd768)
  );
  a_step_inc80: assert property (
    (SAMPLE_ACT && (DATA[2:0] == 3'd5)) |=> 
      ADPCM_STEP == (($past(ADPCM_STEP) <= 10'd688) ? $past(ADPCM_STEP)+10'd80 : 10'd768)
  );
  a_step_inc112: assert property (
    (SAMPLE_ACT && (DATA[2:0] == 3'd6)) |=> 
      ADPCM_STEP == (($past(ADPCM_STEP) <= 10'd656) ? $past(ADPCM_STEP)+10'd112 : 10'd768)
  );
  a_step_inc144: assert property (
    (SAMPLE_ACT && (DATA[2:0] == 3'd7)) |=> 
      ADPCM_STEP == (($past(ADPCM_STEP) <= 10'd624) ? $past(ADPCM_STEP)+10'd144 : 10'd768)
  );

  // Minimal, meaningful coverage
  c_keyon:         cover property (KEYON && !KEYOFF);
  c_two_nibbles:   cover property (SAMPLE_ACT && !NIBBLE ##1 SAMPLE_ACT && NIBBLE);
  c_stop_reached:  cover property (RUN && CLK_SAMP && STOP_EQ && !SET_FLAG);
  c_endflag_clear: cover property (RUN && CLK_SAMP && FLAGMASK && !PREV_FLAGMASK ##1 (END_FLAG == 1'b0));
  c_step_dec:      cover property (SAMPLE_ACT && (DATA[2:0] inside {3'd0,3'd1,3'd2,3'd3}));
  c_step_inc4:     cover property (SAMPLE_ACT && (DATA[2:0] == 3'd4));
  c_step_inc5:     cover property (SAMPLE_ACT && (DATA[2:0] == 3'd5));
  c_step_inc6:     cover property (SAMPLE_ACT && (DATA[2:0] == 3'd6));
  c_step_inc7:     cover property (SAMPLE_ACT && (DATA[2:0] == 3'd7));
  c_se_pos:        cover property (SAMPLE_ACT ##1 (SAMPLE_OUT[15:12] == 4'h0));
  c_se_neg:        cover property (SAMPLE_ACT ##1 (SAMPLE_OUT[15:12] == 4'hF));
endmodule

bind ch_pcma ch_pcma_sva sva_ch_pcma();