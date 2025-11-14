// SVA for adv3224
// Bind this module to the DUT instance
//   bind adv3224 adv3224_sva #(.DIV(divider)) i_adv3224_sva();

module adv3224_sva #(parameter int DIV = 5) ();
  // Access DUT scope via bind (no ports needed)
  // Assumes all names below are from adv3224

  localparam int HALF = DIV/2;

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Constant/combinational mappings
  ap_const_ce:       assert property (cps_ce_n == 1'b0);
  ap_const_resetn:   assert property (cps_reset_n == !reset);
  ap_readdata_map:   assert property (avs_slave_readdata == {7'b0, shift_busy});
  ap_clk_map:        assert property (cps_clk == (clk_en ? div_clk : 1'b1));
  ap_update_map:     assert property (cps_update_n == ((~clk_en && shift_busy) ? ~div_clk : 1'b1));
  ap_datain_map:     assert property (cps_datain == shift_buffer[39]);
  ap_clk_gating:     assert property (!clk_en |-> cps_clk == 1'b1);

  // Reset defaults (checked while reset is asserted)
  ap_reset_defaults: assert property (@(posedge clk)
                        reset |-> (clk_counter==9'd1 && div_clk==1'b1 &&
                                   clk_en==1'b0 && shift_busy==1'b0 &&
                                   shift_counter==6'd0 &&
                                   outputs[0]==5'b0 && outputs[1]==5'b0 &&
                                   outputs[2]==5'b0 && outputs[3]==5'b0 &&
                                   outputs[4]==5'b0 && outputs[5]==5'b0 &&
                                   outputs[6]==5'b0 && outputs[7]==5'b0));

  // Idle state holds these values
  ap_idle_vals:      assert property (!shift_busy |-> (clk_counter==9'd1 && shift_counter==6'd0 && div_clk==1'b1));

  // Counter range constraints
  ap_clkctr_range:   assert property (clk_counter inside {[9'd1:9'(HALF)]});
  ap_shiftcnt_range: assert property (shift_counter inside {[6'd0:6'd39]});

  // Start command behavior (write with bit7 set when idle)
  ap_start_load:     assert property (!shift_busy && avs_slave_write && avs_slave_writedata[7]
                                      |=> (shift_busy && clk_en &&
                                           shift_buffer == {outputs[7],outputs[6],outputs[5],outputs[4],
                                                            outputs[3],outputs[2],outputs[1],outputs[0]}));

  // Register write (bit7 clear) updates addressed outputs when idle
  ap_prog_out:       assert property (!shift_busy && avs_slave_write && !avs_slave_writedata[7]
                                      |=> outputs[avs_slave_address] ==
                                          {~avs_slave_writedata[4], avs_slave_writedata[3:0]});

  // Writes during busy do not change programmed outputs
  ap_write_ignored_busy:
                      assert property (shift_busy && avs_slave_write |-> $stable({outputs[0],outputs[1],outputs[2],outputs[3],
                                                                                     outputs[4],outputs[5],outputs[6],outputs[7]}));

  // Clock-divider/counter behavior while busy:
  // Case 1: previous clk_counter hit HALF -> reset counter to 1 and toggle div_clk
  ap_div_toggle:     assert property ($past(shift_busy) && $past(clk_counter)==HALF
                                      |-> (clk_counter==9'd1 && div_clk==$past(!div_clk)));

  // Case 1a: on div_clk rising sampling point (prev div_clk==0) and enabled, shift progress
  ap_shift_step:     assert property ($past(shift_busy) && $past(clk_counter)==HALF &&
                                      !$past(div_clk) && $past(clk_en) && ($past(shift_counter)!=6'd39)
                                      |-> (shift_counter==$past(shift_counter)+1 &&
                                           shift_buffer==$past(shift_buffer)<<1));

  // Case 1b: terminal bit reached -> drop clk_en
  ap_drop_clk_en:    assert property ($past(shift_busy) && $past(clk_counter)==HALF &&
                                      !$past(div_clk) && $past(clk_en) && ($past(shift_counter)==6'd39)
                                      |-> (clk_en==1'b0));

  // Case 1c: when clk_en already low at sampling point -> clear busy
  ap_clear_busy:     assert property ($past(shift_busy) && $past(clk_counter)==HALF &&
                                      !$past(div_clk) && !$past(clk_en)
                                      |-> (shift_busy==1'b0));

  // Case 1d: when sampling at prev div_clk==1, no shift-side effects occur
  ap_no_shift_on_fall: assert property ($past(shift_busy) && $past(clk_counter)==HALF &&
                                        $past(div_clk)
                                        |-> ($stable(shift_counter) && $stable(shift_buffer) &&
                                             $stable(clk_en) && $stable(shift_busy)));

  // Case 2: previous clk_counter not HALF -> increment and hold div_clk
  ap_div_count:      assert property ($past(shift_busy) && $past(clk_counter)!=HALF
                                      |-> (clk_counter==$past(clk_counter)+1 && div_clk==$past(div_clk)));

  // Liveness: a start must complete within a bounded number of cycles
  localparam int MAX_LAT = (2*HALF*(41))+8;
  ap_transfer_completes:
                      assert property (!shift_busy && avs_slave_write && avs_slave_writedata[7]
                                        |=> ##[1:MAX_LAT] !shift_busy);

  // Coverage
  cv_start:          cover property (!shift_busy && avs_slave_write && avs_slave_writedata[7]);
  cv_prog:           cover property (!shift_busy && avs_slave_write && !avs_slave_writedata[7]);
  cv_shift_progress: cover property ($past(shift_busy) && $past(clk_counter)==HALF && !$past(div_clk) &&
                                     $past(clk_en) && shift_counter==$past(shift_counter)+1);
  cv_update_pulse:   cover property ($past(shift_busy) && $past(clk_counter)==HALF && !$past(div_clk) &&
                                     !$past(clk_en) ##1 !shift_busy);
endmodule

bind adv3224 adv3224_sva #(.DIV(divider)) i_adv3224_sva();