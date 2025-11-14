// SVA for or4 and or2. Bind these into the DUTs. Concise, full functional checks and key coverage.

module or4_sva(
    input  logic A, B, C, D,
    input  logic X,
    input  logic or1_out, or2_out,
    input  logic VPWR, VPB, VNB, VGND
);
  default clocking cb @(*); endclocking

  // Power rails sanity (locals declared as supplies in DUT)
  ap_pwrs: assert property (VPWR===1'b1 && VPB===1'b1 && VGND===1'b0 && VNB===1'b0);

  // Structural decomposition correctness
  ap_or1:  assert property (or1_out === (A | B));
  ap_or2:  assert property (or2_out === (C | D));
  ap_join: assert property (X === (or1_out | or2_out));

  // End-to-end functional equivalence with X-propagation guard
  ap_func: assert property ((!$isunknown({A,B,C,D})) |-> (X === (A|B|C|D)));

  // Basic functional coverage
  cp_all0:      cover property (!A && !B && !C && !D && !X);
  cp_onlyA:     cover property ( A && !B && !C && !D &&  X);
  cp_onlyB:     cover property (!A &&  B && !C && !D &&  X);
  cp_onlyC:     cover property (!A && !B &&  C && !D &&  X);
  cp_onlyD:     cover property (!A && !B && !C &&  D &&  X);
  cp_all1:      cover property ( A &&  B &&  C &&  D &&  X);
  cp_x_rise:    cover property ($rose(X));
  cp_x_fall:    cover property ($fell(X));
endmodule

bind or4 or4_sva o4_chk (
  .A(A), .B(B), .C(C), .D(D), .X(X),
  .or1_out(or1_out), .or2_out(or2_out),
  .VPWR(VPWR), .VPB(VPB), .VNB(VNB), .VGND(VGND)
);

// Reusable SVA for the leaf or2 gates
module or2_sva(
  input logic A, B, X
);
  default clocking cb @(*); endclocking

  ap_eq:    assert property (X === (A | B));
  ap_known: assert property ((!$isunknown({A,B})) |-> (X === (A|B)));

  cp_00:    cover property (!A && !B && !X);
  cp_10:    cover property ( A && !B &&  X);
  cp_01:    cover property (!A &&  B &&  X);
  cp_11:    cover property ( A &&  B &&  X);
  cp_rise:  cover property ($rose(X));
  cp_fall:  cover property ($fell(X));
endmodule

bind or2 or2_sva o2_chk (.A(A), .B(B), .X(X));