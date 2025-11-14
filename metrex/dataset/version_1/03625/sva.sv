// SVA for SSCG
// Bind into the DUT to access internal signals directly
bind SSCG SSCG_SVA u_SSCG_SVA();

module SSCG_SVA;

  // Access DUT scope signals directly via bind
  // clk_in, clk_en, sscg_freq, clk_out, fm_accumulator, fm_increment, fm_modulation, clk_output, PERIOD

  default clocking cb @(posedge clk_in); endclocking

  // Gate assertions until we have a valid past sample
  logic past_valid;
  initial past_valid = 0;
  always @(posedge clk_in) past_valid <= 1'b1;
  default disable iff (!past_valid);

  // Sanity: internal state and output are never X/Z after first cycle
  assert property (!$isunknown({clk_out, clk_output, fm_accumulator, fm_increment, fm_modulation}));

  // fm_increment must be the constant PERIOD and never change
  assert property (fm_increment == PERIOD);
  assert property ($stable(fm_increment));

  // fm_accumulator next-state function
  assert property (
    fm_accumulator ==
      ( $past(clk_en) ? ($past(fm_accumulator) + $past(fm_increment))
                      :  $past(fm_accumulator) )
  );

  // fm_modulation next-state function
  assert property (
    fm_modulation ==
      ( $past(clk_en) ? ($past(sscg_freq) >> 1)
                      :  $past(fm_modulation) )
  );

  // clk_output next-state function
  // Uses pre-update fm_accumulator and fm_modulation when enabled; samples clk_in (->1) when disabled
  assert property (
    clk_output ==
      ( $past(clk_en) ? ((( $past(fm_accumulator) + $past(fm_modulation) ) >> 1)[0])
                      :  1'b1 )
  );

  // Output port must mirror the register
  assert property (clk_out == clk_output);

  // When disabled for 2+ consecutive cycles, clk_out must remain high
  assert property ( !clk_en ##1 !clk_en |-> (clk_out == 1'b1) );

  // Coverage: enable/disable edges
  cover property ($rose(clk_en));
  cover property ($fell(clk_en));

  // Coverage: output toggles while enabled
  cover property ( $past(clk_en) && (clk_output != $past(clk_output)) );

  // Coverage: accumulator wraparound while enabled
  cover property ( $past(clk_en) && (fm_accumulator < $past(fm_accumulator)) );

  // Coverage: sscg_freq changes while enabled (modulation tracking exercised)
  cover property ( $past(clk_en) && $changed(sscg_freq) );

endmodule