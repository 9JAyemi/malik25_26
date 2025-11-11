// Concise, high-quality SVA for idelay_ctrl_rdy_module and IDELAYCTRL

// Bind into the top to check AND-combine, reset behavior, and coverage
module idelay_ctrl_rdy_module_sva;
  default clocking cb @(posedge clk200); endclocking

  // No X on key signals
  assert property ( ! $isunknown({rst200, idelay_ctrl_rdy, idelay_ctrl_rdy_x0y5, idelay_ctrl_rdy_x0y6}) );

  // Output equals AND of internal RDYs
  assert property ( idelay_ctrl_rdy == (idelay_ctrl_rdy_x0y5 & idelay_ctrl_rdy_x0y6) );

  // If reset held for >=1 full cycle, both RDYs must be low
  assert property ( rst200 && $past(rst200) |-> (!idelay_ctrl_rdy_x0y5 && !idelay_ctrl_rdy_x0y6) );

  // After a clean falling edge of reset, RDYs and output assert on the next clock
  assert property ( $fell(rst200) ##1 !rst200 |-> (idelay_ctrl_rdy_x0y5 && idelay_ctrl_rdy_x0y6 && idelay_ctrl_rdy) );

  // Once output high and reset stays low, it must remain high
  assert property ( !$past(rst200) && !rst200 && $past(idelay_ctrl_rdy) |-> idelay_ctrl_rdy );

  // Coverage
  cover property ( rst200 ##1 !rst200 ##1 idelay_ctrl_rdy ); // reset-release -> ready
  cover property ( $fell(rst200) ##1 (idelay_ctrl_rdy_x0y5 && idelay_ctrl_rdy_x0y6 && idelay_ctrl_rdy) );
  cover property ( $rose(rst200) ##1 (!idelay_ctrl_rdy_x0y5 && !idelay_ctrl_rdy_x0y6 && !idelay_ctrl_rdy) );
endmodule

// Bind into each IDELAYCTRL instance to verify generic behavior
module IDELAYCTRL_sva;
  default clocking cb @(posedge REFCLK); endclocking

  // No X on key signals
  assert property ( ! $isunknown({RST, RDY}) );

  // While reset held across a full cycle, RDY must be low
  assert property ( RST && $past(RST) |-> !RDY );

  // On reset rise, RDY must drop within 1 cycle (allowing async/same-cycle ordering)
  assert property ( $rose(RST) |-> ##1 !RDY );

  // After a clean reset fall, RDY asserts on the next clock
  assert property ( $fell(RST) ##1 !RST |-> RDY );

  // Once high and reset stays low, RDY must remain high
  assert property ( !$past(RST) && !RST && $past(RDY) |-> RDY );

  // Coverage
  cover property ( $fell(RST) ##1 RDY );
  cover property ( $rose(RST) ##1 RST ##1 !RST ##1 RDY );
endmodule

// Bind statements
bind idelay_ctrl_rdy_module idelay_ctrl_rdy_module_sva;
bind IDELAYCTRL           IDELAYCTRL_sva;