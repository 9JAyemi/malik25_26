// SVA for lo_read – bind these into the DUT for checks and coverage
bind lo_read lo_read_sva sva();

module lo_read_sva;
  // Bound inside lo_read: direct visibility of DUT internals/ports
  default clocking cb @(posedge pck0); endclocking

  bit past_valid;
  always @(posedge pck0) past_valid <= 1'b1;

  // Common predicates
  let cap        = (pck_cnt == 8'd7) && !pck_divclk;
  let frame_expr = (pck_cnt[7:3] == 5'd1) && !pck_divclk;

  // Combinational relations (sampled on pck0)
  assert property (ssp_clk   == pck0);
  assert property (ssp_frame == frame_expr);
  assert property (ssp_din   == (to_arm_shiftreg[7] && !pck_divclk));
  assert property (pwr_hi    == 1'b0);
  assert property (pwr_oe1   == 1'b0);
  assert property (pwr_oe2   == 1'b0);
  assert property (pwr_oe3   == 1'b0);
  assert property (pwr_oe4   == 1'b0);
  assert property (pwr_lo    == (lf_field & pck_divclk));
  assert property (adc_clk   == ~pck_divclk);
  assert property (dbg       == adc_clk);

  // Check both phases/edges for clocks and gating
  assert property (@(negedge pck0) ssp_clk == 1'b0);
  assert property (@(posedge pck_divclk or negedge pck_divclk)
                   (adc_clk == ~pck_divclk) && (dbg == adc_clk));
  assert property (pck_divclk |-> !ssp_din);

  // Shift-register behavior
  assert property (disable iff (!past_valid)
                   cap |-> to_arm_shiftreg == $past(adc_d));
  assert property (disable iff (!past_valid)
                   !cap |-> to_arm_shiftreg == {$past(to_arm_shiftreg[6:0]), 1'b0});

  // Minimal functional coverage
  cover property (cap);
  cover property (ssp_frame);
  cover property (ssp_din);
  cover property (pwr_lo);
  cover property (@(posedge pck_divclk) 1);
  cover property (@(negedge pck_divclk) 1);
  cover property (@(posedge pck0)  $rose(ssp_clk));
  cover property (@(negedge pck0)  $fell(ssp_clk));
endmodule