// SVA for full_adder. Bind to DUT; checks golden behavior and internal structure.
// Clockless concurrent properties for combinational logic.

module full_adder_sva (
  input logic A, B, CIN,
  input logic SUM, COUT,
  input logic S1, C1, C2,
  input logic fa2_CI
);

  // Sanity: no X/Z anywhere (ports and key internals)
  assert property (!$isunknown({A,B,CIN,SUM,COUT,S1,C1,C2,fa2_CI}));

  // Golden end-to-end behavior
  assert property ({COUT,SUM} == A + B + CIN);
  assert property (SUM  == (A ^ B ^ CIN));
  assert property (COUT == ((A & B) | (A & CIN) | (B & CIN)));

  // Structural checks vs. intended decomposition
  assert property ({C1,S1} == A + B + CIN);
  assert property (fa2_CI == 1'b0);
  assert property ({C2,SUM} == (S1 + C1));
  assert property (COUT == (C1 | C2));

  // Full functional coverage of all input combinations with expected outputs
  cover property (A==0 && B==0 && CIN==0 && {COUT,SUM}==2'd0);
  cover property (A==0 && B==0 && CIN==1 && {COUT,SUM}==2'd1);
  cover property (A==0 && B==1 && CIN==0 && {COUT,SUM}==2'd1);
  cover property (A==0 && B==1 && CIN==1 && {COUT,SUM}==2'd2);
  cover property (A==1 && B==0 && CIN==0 && {COUT,SUM}==2'd1);
  cover property (A==1 && B==0 && CIN==1 && {COUT,SUM}==2'd2);
  cover property (A==1 && B==1 && CIN==0 && {COUT,SUM}==2'd2);
  cover property (A==1 && B==1 && CIN==1 && {COUT,SUM}==2'd3);

endmodule

bind full_adder full_adder_sva sva (
  .A(A), .B(B), .CIN(CIN), .SUM(SUM), .COUT(COUT),
  .S1(S1), .C1(C1), .C2(C2),
  .fa2_CI(fa2.CI)
);