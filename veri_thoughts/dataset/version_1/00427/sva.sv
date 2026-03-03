// SVA for carry_lookahead_multiplier
// Bind this file to the DUT: bind carry_lookahead_multiplier cla_mult_sva;

module cla_mult_sva;

  // Reset behavior (must zero result on any cycle reset is 1)
  assert property (@(posedge clk) reset |-> result == 16'h0000)
    else $error("Result not cleared on reset");

  // Use a default clock and disable assertions during reset for the rest
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Sanity: no X/Z on key IOs when not in reset
  assert property (!$isunknown({a,b,reset}))
    else $error("X/Z on inputs");

  // No X/Z on result when not in reset
  assert property (!$isunknown(result))
    else $error("X/Z on result");

  // Core functionality: sequential concatenation (1-cycle latency)
  // Guard with $past(!reset) to avoid first-cycle $past hazards
  assert property ((!reset && $past(!reset)) |-> result == { $past(b), $past(a) })
    else $error("Result != {b,a} from prior cycle");

  // Arithmetic form equivalence (as implemented)
  assert property ((!reset && $past(!reset)) |-> result == ($past({8'h00,a}) + ($past({8'h00,b}) << 8)))
    else $error("Result != zero-extended add/shift form from prior cycle");

  // Structural sanity on partial products and generates (width/replication correctness)
  // These catch common width/replication bugs like using a & b[i] instead of a & {8{b[i]}}
  genvar gi;
  generate
    for (gi = 0; gi < 8; gi++) begin : P_G_CHECKS
      assert property (p[gi] == (a & {8{b[gi]}}))
        else $error("p[%0d] mismatch: expect a & {8{b[%0d]}}", gi, gi);
      assert property (g[gi] == (a | {8{b[gi]}}))
        else $error("g[%0d] mismatch: expect a | {8{b[%0d]}}", gi, gi);
    end
  endgenerate

  // Carry chain knownness (c[0] must be driven; propagates to all)
  generate
    for (genvar cj = 0; cj <= 8; cj++) begin : C_KNOWN
      assert property (!$isunknown(c[cj]))
        else $error("c[%0d] has X/Z", cj);
    end
  endgenerate

  // Lightweight coverage
  cover property ($fell(reset));                                    // reset deassertion seen
  cover property ((!reset && $past(!reset)) && result == { $past(b), $past(a) }); // normal update
  cover property ((!reset && $past(!reset)) && $past(a)==8'h00 && $past(b)==8'h00 && result==16'h0000);
  cover property ((!reset && $past(!reset)) && $past(a)==8'hFF && $past(b)==8'hFF && result==16'hFFFF);
  cover property ((!reset && $past(!reset)) && $past(a)==8'h01 && $past(b)==8'h80 && result==16'h8001);

endmodule

bind carry_lookahead_multiplier cla_mult_sva;