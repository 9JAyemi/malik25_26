// SVA for any_edge_detector: checks function and internal state concisely
// Bind into the DUT so we can see internal prev_in
module any_edge_detector_sva;
  default clocking cb @(posedge clk); endclocking

  // Track past-valid to avoid first-cycle $past issues
  bit past1, past2;
  initial begin past1 = 0; past2 = 0; end
  always @(posedge clk) begin
    past1 <= 1;
    past2 <= past1;
  end

  // Internal state must track prior input
  assert property (past1 |-> (prev_in == $past(in)))
    else $error("prev_in != $past(in)");

  // Functional equivalence: output is a 1-cycle-late rising-edge detect
  assert property (past2 |-> (anyedge == ($past(in) & ~ $past(in,2))))
    else $error("anyedge != $past(in) & ~ $past(in,2)");

  // One-cycle pulse max (no back-to-back pulses on any bit)
  assert property (past1 |-> ((anyedge & $past(anyedge)) == '0))
    else $error("anyedge held >1 cycle");

  // anyedge only from previously high bits (no spurious pulses after falls)
  assert property (past1 |-> ((anyedge & ~$past(in)) == '0))
    else $error("anyedge asserted on bit that was 0 in prior cycle");

  // Sanity: no X on output
  assert property (past1 |-> !$isunknown(anyedge))
    else $error("anyedge has X/Z");

  // Coverage: per-bit rising and falling behavior, and multi-bit rises
  genvar i;
  generate
    for (i = 0; i < 8; i++) begin : C
      cover property (past2 && $rose(in[i]) ##1 anyedge[i]);
      cover property (past2 && $fell(in[i]) ##1 !anyedge[i]);
    end
  endgenerate
  cover property (past2 && ($countones(in & ~$past(in)) >= 2) ##1 ($countones(anyedge) >= 2));
endmodule

bind any_edge_detector any_edge_detector_sva();