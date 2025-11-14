// SVA for clock_generator
module clock_generator_sva;
  // Bind scope gives access to clk, cyc, genthiscyc, genclk
  default clocking cb @(posedge clk); endclocking
  bit past_valid;
  initial past_valid = 0;
  always @(posedge clk) past_valid <= 1'b1;
  default disable iff (!past_valid);

  // Basic counter behavior
  ap_cyc_inc:        assert property (cyc == $past(cyc) + 8'h1);

  // Genthiscyc should match LSB of current cyc
  ap_genthis_equiv:  assert property (genthiscyc == cyc[0]);

  // Genclk behavior in lower/upper half of count space
  ap_gen_lower:      assert property (($past(cyc) <  8'h80) |-> genclk == $past(genthiscyc));
  ap_gen_upper:      assert property (($past(cyc) >= 8'h80) |-> genclk == ~$past(genclk));

  // Consequence: genclk toggles every cycle
  ap_gen_toggles:    assert property (genclk == ~$past(genclk));

  // No X/Z after first cycle
  ap_no_x:           assert property (!$isunknown({cyc, genclk, genthiscyc}));

  // Coverage
  cv_lower_hit:      cover  property (($past(cyc) <  8'h80) && (genclk == $past(genthiscyc)));
  cv_upper_hit:      cover  property (($past(cyc) >= 8'h80) && (genclk == ~$past(genclk)));
  cv_boundary_7F80:  cover  property (($past(cyc) == 8'h7F) && (cyc == 8'h80));
  cv_wrap_FF00:      cover  property (($past(cyc) == 8'hFF) && (cyc == 8'h00));
endmodule

bind clock_generator clock_generator_sva cg_sva();