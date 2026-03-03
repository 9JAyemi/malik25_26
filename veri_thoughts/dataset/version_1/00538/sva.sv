// SVA for latch_module
module latch_module_sva (input logic CLK, EN, TE, ENCLK);

  default clocking cb @(posedge CLK); endclocking

  // past-valid guard (no reset in DUT)
  logic past_valid;
  initial past_valid = 1'b0;
  always @(cb) past_valid <= 1'b1;

  default disable iff (!past_valid)

  // Golden next-state relation
  // ENCLK(n) == EN(n-1) ? TE(n-1) : ENCLK(n-1)
  assert property (ENCLK == ($past(EN) ? $past(TE) : $past(ENCLK)))
    else $error("ENCLK next-state mismatch");

  // Any ENCLK change must be caused by a prior enable, and must equal prior TE
  assert property ($changed(ENCLK) |-> ($past(EN) && (ENCLK == $past(TE))))
    else $error("ENCLK changed without prior EN or mismatched TE");

  // Output should never be X/Z after first cycle
  assert property (!$isunknown(ENCLK))
    else $error("ENCLK is X/Z");

  // Coverage: update to 1
  cover property (EN && TE |=> ENCLK);

  // Coverage: update to 0
  cover property (EN && !TE |=> !ENCLK);

  // Coverage: hold when disabled for at least one cycle
  cover property (!EN |=> $stable(ENCLK));

  // Coverage: back-to-back enables with different TE values
  cover property ((EN && TE) ##1 (EN && !TE));

endmodule

// Bind into DUT
bind latch_module latch_module_sva u_latch_module_sva (.*);