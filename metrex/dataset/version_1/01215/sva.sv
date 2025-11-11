// SVA checker for edge_detector
// Binds into DUT and verifies pipeline, swap, and update semantics concisely.

module edge_detector_sva;
  default clocking cb @(posedge clk); endclocking

  // past-valid tracking
  logic past1, past2;
  always_ff @(posedge clk) begin
    past1 <= 1'b1;
    past2 <= past1;
  end

  // Pipeline capture checks
  // in_reg1 <= in; in_reg2 <= in_reg1;
  assert property (disable iff (!past1) in_reg1 == $past(in));
  assert property (disable iff (!past2) in_reg2 == $past(in_reg1));

  // out_reg swap checks: out_reg1 <= out_reg2; out_reg2 <= out_reg1;
  assert property (disable iff (!past1) out_reg1 == $past(out_reg2));
  assert property (disable iff (!past1) out_reg2 == $past(out_reg1));
  // 2-cycle periodicity implied by swap
  assert property (disable iff (!past2) out_reg1 == $past(out_reg1,2));
  assert property (disable iff (!past2) out_reg2 == $past(out_reg2,2));

  // Edge-detect/update semantics (uses old pipeline values)
  // Update occurs only on detected falling edge of bit 0 (in_reg2=1, in_reg1=0 from last cycle)
  assert property (disable iff (!past1)
                   $past(in_reg2[0] && !in_reg1[0]) |-> anyedge == $past(out_reg2));

  // No update otherwise (register holds value if condition not met)
  assert property (disable iff (!past1)
                   !$past(in_reg2[0] && !in_reg1[0]) |-> anyedge == $past(anyedge));

  // Any change of anyedge must be due to that falling-edge condition
  assert property (disable iff (!past1)
                   (anyedge != $past(anyedge)) |-> $past(in_reg2[0] && !in_reg1[0]));

  // Rising edge on bit 0 must not update
  assert property (disable iff (!past1)
                   $past(!in_reg2[0] && in_reg1[0]) |-> anyedge == $past(anyedge));

  // Coverage
  cover property (past1 && $past(in_reg2[0] && !in_reg1[0]));            // saw a falling edge
  cover property (past1 && $past(!in_reg2[0] && in_reg1[0]));            // saw a rising edge
  cover property (past1 && (anyedge != $past(anyedge)));                 // anyedge changed
  cover property (past2 && out_reg1 == $past(out_reg1,2) &&
                         out_reg2 == $past(out_reg2,2));                 // swap activity
endmodule

bind edge_detector edge_detector_sva sva_i();