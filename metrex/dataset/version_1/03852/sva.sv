// SVA for my_module
// Bind into DUT; checks functional correctness, X-propagation, and basic coverage.

bind my_module my_module_sva u_my_module_sva (
  .A1(A1), .A2(A2), .B1(B1), .C1(C1), .D1(D1),
  .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB),
  .Y(Y)
);

module my_module_sva (
  input  logic A1, A2, B1, C1, D1,
  input  logic VPWR, VGND, VPB, VNB,
  input  logic Y
);
  // Power-good gating
  wire pg = (VPWR === 1'b1) && (VGND === 1'b0) && (VPB === 1'b1) && (VNB === 1'b0);
  wire [3:0] v = {A1, A2, B1, C1};

  default clocking cb @(*); endclocking
  default disable iff (!pg)

  // Functional equivalence: Y is 1 iff all four data inputs are all 1s or all 0s
  // Compact spec: Y == (&v) | (~|v)
  assert property (Y === ((&v) | (~|v)))
    else $error("my_module: Y mismatches spec (&v)|(~|v)");

  // No X on Y when inputs are known
  assert property (!$isunknown(v) |-> !$isunknown(Y))
    else $error("my_module: Y is X/Z while inputs are known");

`ifdef FORMAL
  // For formal runs, constrain power rails to valid values
  assume property (pg);
`endif

  // Functional coverage
  // Cover Y=1 via all-ones
  cover property (pg && (&v) && Y);
  // Cover Y=1 via all-zeros
  cover property (pg && (~|v) && Y);
  // Cover mixed inputs => Y=0
  cover property (pg && !( &v || ~|v ) && !Y);
  // Observe both edges of Y under power-good
  cover property ($rose(Y));
  cover property ($fell(Y));
endmodule