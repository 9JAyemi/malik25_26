// SVA for Clock_Gating_Module
// Bindable, concise checks and coverage

module Clock_Gating_Module_sva (Clock_Gating_Module dut);

  // Sample on any relevant edge
  default clocking cb @(
      posedge dut.CLK or negedge dut.CLK or
      posedge dut.EN  or negedge dut.EN  or
      posedge dut.TE  or negedge dut.TE  or
      posedge dut.RESET or negedge dut.RESET
  ); endclocking

  // No X/Z on IOs
  a_no_x: assert property( !$isunknown({dut.CLK,dut.EN,dut.TE,dut.RESET,dut.ENCLK}) );

  // Functional equivalence: ENCLK = TE ^ (EN & ~RESET & CLK)
  a_func: assert property( dut.ENCLK == (dut.TE ^ (dut.EN && !dut.RESET && dut.CLK)) );

  // Explicit modes
  a_off_bypass: assert property( (!dut.EN || dut.RESET) |-> (dut.ENCLK == dut.TE) );
  a_on_te0:     assert property( ( dut.EN && !dut.RESET && !dut.TE) |-> (dut.ENCLK == dut.CLK) );
  a_on_te1:     assert property( ( dut.EN && !dut.RESET &&  dut.TE) |-> (dut.ENCLK == ~dut.CLK) );

  // Edge alignment when enabled
  a_on_te0_rise: assert property( @(posedge dut.CLK) (dut.EN && !dut.RESET && !dut.TE) |-> $rose(dut.ENCLK) );
  a_on_te0_fall: assert property( @(negedge dut.CLK) (dut.EN && !dut.RESET && !dut.TE) |-> $fell(dut.ENCLK) );
  a_on_te1_rise: assert property( @(posedge dut.CLK) (dut.EN && !dut.RESET &&  dut.TE) |-> $fell(dut.ENCLK) );
  a_on_te1_fall: assert property( @(negedge dut.CLK) (dut.EN && !dut.RESET &&  dut.TE) |-> $rose(dut.ENCLK) );

  // When disabled, CLK edges must not affect ENCLK
  a_off_clk_no_effect: assert property( @(posedge dut.CLK or negedge dut.CLK)
                                        (!dut.EN || dut.RESET) |-> $stable(dut.ENCLK) );

  // Safe gating protocol (avoid glitches): EN/RESET change only when CLK is low
  a_en_change_when_clk_low:  assert property( @(posedge dut.EN    or negedge dut.EN)    !dut.CLK );
  a_rst_change_when_clk_low: assert property( @(posedge dut.RESET or negedge dut.RESET) !dut.CLK );

  // Coverage
  c_on_te0_pos: cover property( @(posedge dut.CLK) (dut.EN && !dut.RESET && !dut.TE && $rose(dut.ENCLK)) );
  c_on_te0_neg: cover property( @(negedge dut.CLK) (dut.EN && !dut.RESET && !dut.TE && $fell(dut.ENCLK)) );
  c_on_te1_pos: cover property( @(posedge dut.CLK) (dut.EN && !dut.RESET &&  dut.TE && $fell(dut.ENCLK)) );
  c_on_te1_neg: cover property( @(negedge dut.CLK) (dut.EN && !dut.RESET &&  dut.TE && $rose(dut.ENCLK)) );
  c_off_pos:    cover property( @(posedge dut.CLK) ((!dut.EN || dut.RESET) && $stable(dut.ENCLK)) );
  c_off_neg:    cover property( @(negedge dut.CLK) ((!dut.EN || dut.RESET) && $stable(dut.ENCLK)) );

  // TE toggling effects (both modes)
  c_te_toggle_off: cover property( @(posedge dut.TE or negedge dut.TE) (!dut.EN || dut.RESET) && $changed(dut.ENCLK) );
  c_te_toggle_on:  cover property( @(posedge dut.TE or negedge dut.TE) ( dut.EN && !dut.RESET) && $changed(dut.ENCLK) );

endmodule

bind Clock_Gating_Module Clock_Gating_Module_sva cgmsva(.dut);