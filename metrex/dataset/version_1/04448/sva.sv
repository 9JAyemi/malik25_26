// SVA for d_ff_reset — concise, quality checks and coverage
module d_ff_reset_sva (
  input  logic D,
  input  logic RESET_B,
  input  logic GATE,
  input  logic VPWR,
  input  logic VGND,
  input  logic VPB,
  input  logic VNB,
  input  logic Q
);
  // Power-good gating (rails and wells)
  wire power_good = (VPWR===1'b1) && (VGND===1'b0) && (VPB===1'b1) && (VNB===1'b0);
  default disable iff (!power_good);

  // Async reset clears immediately
  assert property (@(negedge RESET_B) 1 |-> (Q==1'b0));

  // Reset dominates clock (even if edges coincide)
  assert property (@(posedge GATE) !RESET_B |-> (Q==1'b0));

  // Sync capture on GATE posedge when not in reset
  // Use $past(D) to sample value at the edge; also check non-X propagation
  assert property (@(posedge GATE)
                   RESET_B && !$isunknown($past(D)) |-> (! $isunknown(Q) && Q == $past(D)));

  // Known on reset assertion
  assert property (@(negedge RESET_B) !$isunknown(Q));

  // Coverage: async reset observed
  cover property (@(negedge RESET_B) Q==1'b0);

  // Coverage: capture 0 and 1
  cover property (@(posedge GATE) RESET_B && ($past(D)===1'b0) && (Q===1'b0));
  cover property (@(posedge GATE) RESET_B && ($past(D)===1'b1) && (Q===1'b1));

  // Coverage: simultaneous clock and reset assertion (reset wins)
  cover property (@(posedge GATE) $fell(RESET_B) && (Q==1'b0));
endmodule

bind d_ff_reset d_ff_reset_sva sva_i (
  .D(D), .RESET_B(RESET_B), .GATE(GATE),
  .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB),
  .Q(Q)
);