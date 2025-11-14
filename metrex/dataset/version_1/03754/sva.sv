// SVA for clock_gate
// Bind into the DUT for concise, high-quality checks and coverage

module clock_gate_sva (clock_gate dut);

  default clocking cb @(posedge dut.CLK); endclocking

  // Guard first-cycle $past() usage
  bit init;
  initial init = 0;
  always @(posedge dut.CLK) init <= 1;

  // Functional equivalence: registered output equals EN&TE sampled on previous posedge
  ap_func: assert property (disable iff (!init) dut.ENCLK == $past(dut.EN & dut.TE));

  // Same-cycle post-NBA check (concise two-branch spec)
  ap_hi_now: assert property ((dut.EN & dut.TE) |-> ##0 dut.ENCLK);
  ap_lo_now: assert property ((!dut.EN | !dut.TE) |-> ##0 !dut.ENCLK);

  // No glitches: output stable between clock edges
  ap_stable_between_edges: assert property (@(negedge dut.CLK) $stable(dut.ENCLK));

  // Output never unknown at sampling edge
  ap_no_x: assert property (!$isunknown(dut.ENCLK));

  // Coverage
  cp_out_rise:  cover property (disable iff (!init) $rose(dut.ENCLK));
  cp_out_fall:  cover property (disable iff (!init) $fell(dut.ENCLK));
  cp_gate_on:   cover property (dut.EN && dut.TE);
  cp_gate_off:  cover property (!(dut.EN && dut.TE));

endmodule

bind clock_gate clock_gate_sva cg_sva();