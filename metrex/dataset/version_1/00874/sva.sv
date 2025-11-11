// SVA for clock_gate. Bind this to the DUT.
module clock_gate_sva (input logic CLK, EN, TE, ENCLK);

  default clocking cb @(posedge CLK); endclocking

  // Functional correctness: output equals EN && TE each rising edge
  a_eq_known: assert property (!$isunknown({EN,TE}) |-> (ENCLK == (EN && TE)))
    else $error("ENCLK != EN&&TE when inputs known");

  // Propagate unknowns: if any input is X/Z at a sample, output must be X at that sample
  a_x_prop:   assert property ($isunknown({EN,TE}) |-> $isunknown(ENCLK))
    else $error("ENCLK not X while inputs have X/Z");

  // No asynchronous glitches: output must not change on negedge (and thus between posedges)
  a_stable_negedge: assert property (@(negedge CLK) $stable(ENCLK))
    else $error("ENCLK changed between posedges");

  // Output only changes in sync with inputs’ boolean result at posedge
  a_change_cause: assert property ($changed(ENCLK) |-> $changed(EN && TE))
    else $error("ENCLK changed without corresponding EN&&TE change");

  // Basic coverage
  c_high:    cover property (ENCLK);
  c_low:     cover property (!ENCLK);
  c_rise:    cover property ($rose(ENCLK));
  c_fall:    cover property ($fell(ENCLK));

  // Exercise all input combinations
  c_00: cover property ({EN,TE} == 2'b00);
  c_01: cover property ({EN,TE} == 2'b01);
  c_10: cover property ({EN,TE} == 2'b10);
  c_11: cover property ({EN,TE} == 2'b11);

  // Single-cycle high pulse on ENCLK
  c_one_pulse: cover property (!$past(ENCLK) && ENCLK ##1 !ENCLK);

endmodule

bind clock_gate clock_gate_sva u_clock_gate_sva (.*);