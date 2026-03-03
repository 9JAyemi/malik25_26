// SVA for clock_gate_module
module clock_gate_module_sva (input CLK, EN, TE, reset, ENCLK);

  default clocking cb @(posedge CLK); endclocking

  // Basic sanity/knowns (outside of reset)
  assert property (disable iff (reset) !$isunknown({EN,TE,ENCLK}));

  // Async reset response and dominance
  assert property (@(posedge reset) ENCLK == 1'b0);
  assert property (reset |-> ENCLK == 1'b0);

  // After reset deasserts, hold 0 until first qualified enable
  assert property ($fell(reset) |-> (ENCLK == 1'b0 until_with (EN && TE)));

  // Functional behavior: toggle when EN && TE, hold otherwise
  assert property (disable iff (reset) (EN && TE) |=> ENCLK == !$past(ENCLK));
  assert property (disable iff (reset) (! (EN && TE)) |=> ENCLK ==  $past(ENCLK));

  // Any observed change must have been commanded by prior EN && TE
  assert property (disable iff (reset) (ENCLK != $past(ENCLK)) |-> $past(EN && TE));

  // Coverage
  cover  property (disable iff (reset) (EN && TE));                // at least one toggle opportunity
  cover  property (disable iff (reset) (EN && TE)[*3]);            // burst of 3 toggles
  cover  property (disable iff (reset) (! (EN && TE))[*3]);        // hold for 3 cycles
  cover  property ($rose(reset) ##1 !reset ##1 (EN && TE));        // toggle after a reset sequence
  cover  property (disable iff (reset) $rose(ENCLK));
  cover  property (disable iff (reset) $fell(ENCLK));

endmodule

// Bind into DUT
bind clock_gate_module clock_gate_module_sva sva_i (.*);