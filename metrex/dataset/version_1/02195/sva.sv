// SVA for sky130_fd_sc_ls__and3b
// Bind this into the DUT to check functionality and cover truth table.

module sky130_fd_sc_ls__and3b_sva (
  input logic A_N, B, C, X,
  input logic not0_out, and0_out_X,
  input logic VPWR, VGND, VPB, VNB
);

  // Power rails must be good
  assert property (@(*) VPWR === 1'b1);
  assert property (@(*) VPB  === 1'b1);
  assert property (@(*) VGND === 1'b0);
  assert property (@(*) VNB  === 1'b0);

  // Internal net correctness (when determinable)
  assert property (@(*) !$isunknown(A_N)               |-> (not0_out   === ~A_N));
  assert property (@(*) !$isunknown({B,C,not0_out})    |-> (and0_out_X === (C & not0_out & B)));
  assert property (@(*) !$isunknown(and0_out_X)        |-> (X === and0_out_X));

  // Functional correctness (deterministic input cases)
  assert property (@(*) (B===1'b0)                     |-> (X===1'b0));
  assert property (@(*) (C===1'b0)                     |-> (X===1'b0));
  assert property (@(*) (A_N===1'b1)                   |-> (X===1'b0));
  assert property (@(*) (A_N===1'b0 && B===1'b1 && C===1'b1) |-> (X===1'b1));

  // Full functional check when inputs are known
  assert property (@(*) !$isunknown({A_N,B,C})         |-> (X === (C & ~A_N & B)));
  assert property (@(*) !$isunknown({A_N,B,C})         |-> !$isunknown(X));

  // Truth-table coverage (all 8 input combinations with expected X)
  cover property (@(*) (A_N===0 && B===0 && C===0 && X===0));
  cover property (@(*) (A_N===0 && B===0 && C===1 && X===0));
  cover property (@(*) (A_N===0 && B===1 && C===0 && X===0));
  cover property (@(*) (A_N===0 && B===1 && C===1 && X===1));
  cover property (@(*) (A_N===1 && B===0 && C===0 && X===0));
  cover property (@(*) (A_N===1 && B===0 && C===1 && X===0));
  cover property (@(*) (A_N===1 && B===1 && C===0 && X===0));
  cover property (@(*) (A_N===1 && B===1 && C===1 && X===0));

  // Output toggle coverage
  cover property (@(*) $rose(X));
  cover property (@(*) $fell(X));

  // X-propagation coverage in non-controlling scenarios
  cover property (@(*) (B===1 && C===1 && $isunknown(A_N) && $isunknown(X)));
  cover property (@(*) (A_N===0 && C===1 && $isunknown(B)  && $isunknown(X)));
  cover property (@(*) (A_N===0 && B===1 && $isunknown(C)  && $isunknown(X)));

endmodule

// Bind into the DUT
bind sky130_fd_sc_ls__and3b sky130_fd_sc_ls__and3b_sva u_and3b_sva (
  .A_N(A_N), .B(B), .C(C), .X(X),
  .not0_out(not0_out), .and0_out_X(and0_out_X),
  .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB)
);