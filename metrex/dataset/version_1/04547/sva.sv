// SVA for sky130_fd_sc_lp__o2bb2a
// Function: X = (~(A1_N & A2_N)) & (B1 | B2)

module o2bb2a_sva (
  input logic X,
  input logic A1_N,
  input logic A2_N,
  input logic B1,
  input logic B2,
  input logic VPWR,
  input logic VGND,
  input logic VPB,
  input logic VNB,
  input logic nand0_out,
  input logic or0_out,
  input logic and0_out_X
);

  wire pwr_good = (VPWR===1'b1 && VGND===1'b0 && VPB===1'b1 && VNB===1'b0);
  wire expected = (~(A1_N & A2_N)) & (B1 | B2);

  default disable iff (!pwr_good);

  // Supply wiring check
  assert property (@(A1_N or A2_N or B1 or B2 or VPWR or VGND or VPB or VNB)
                   pwr_good);

  // Pure functional equivalence when inputs are 2-state
  assert property (@(A1_N or A2_N or B1 or B2)
                   !$isunknown({A1_N,A2_N,B1,B2}) |-> (X == expected));

  // No X on output when inputs are 2-state
  assert property (@(A1_N or A2_N or B1 or B2)
                   !$isunknown({A1_N,A2_N,B1,B2}) |-> !$isunknown(X));

  // Deterministic controlling-value checks (robust to Xs elsewhere)
  assert property (@(B1 or B2) (B1===1 || B2===1) && (A1_N===0 || A2_N===0) |-> X===1);
  assert property (@(B1 or B2) (B1===0 && B2===0) |-> X===0);
  assert property (@(A1_N or A2_N) (A1_N===1 && A2_N===1) |-> X===0);

  // Internal net consistency with gate-level structure
  assert property (@(A1_N or A2_N) nand0_out   === ~(A1_N & A2_N));
  assert property (@(B1 or B2)     or0_out     ===  (B1 | B2));
  assert property (@(nand0_out or or0_out) and0_out_X === (nand0_out & or0_out));
  assert property (@(and0_out_X or X) X === and0_out_X);

  // Output toggle coverage
  cover property (@(A1_N or A2_N or B1 or B2) X==0 ##1 X==1);
  cover property (@(A1_N or A2_N or B1 or B2) X==1 ##1 X==0);

  // Input space coverage (all 16 combinations)
  covergroup cg_inputs @(A1_N or A2_N or B1 or B2);
    coverpoint A1_N;
    coverpoint A2_N;
    coverpoint B1;
    coverpoint B2;
    cross A1_N, A2_N, B1, B2;
  endgroup
  cg_inputs cg_inputs_i = new();

  // Functional hit coverage
  cover property (@(A1_N or A2_N or B1 or B2) (X===1));
  cover property (@(A1_N or A2_N or B1 or B2) (X===0));

endmodule

bind sky130_fd_sc_lp__o2bb2a o2bb2a_sva o2bb2a_sva_i (
  .X(X),
  .A1_N(A1_N),
  .A2_N(A2_N),
  .B1(B1),
  .B2(B2),
  .VPWR(VPWR),
  .VGND(VGND),
  .VPB(VPB),
  .VNB(VNB),
  .nand0_out(nand0_out),
  .or0_out(or0_out),
  .and0_out_X(and0_out_X)
);