// SVA for nand4 and nand2

module nand4_sva (input logic A,B,C,D, input logic nand1_out, nand2_out, input logic Y);
  default clocking cb @ (A or B or C or D); endclocking

  // Functional correctness (ports)
  assert property ( !$isunknown({A,B,C,D}) |-> ##0 (Y === ((A & B) | (C & D))) );

  // Structural correctness (internals)
  assert property ( !$isunknown({A,B}) |-> ##0 (nand1_out === ~(A & B)) );
  assert property ( !$isunknown({C,D}) |-> ##0 (nand2_out === ~(C & D)) );
  assert property ( ##0 (Y === ~(nand1_out & nand2_out)) );

  // No X on Y when inputs are known
  assert property ( !$isunknown({A,B,C,D}) |-> ##0 !$isunknown(Y) );

  // Coverage: all input combinations and Y toggles
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : cov_vecs
      cover property ( ##0 ({A,B,C,D} == i[3:0]) );
    end
  endgenerate
  cover property ( ##0 $rose(Y) );
  cover property ( ##0 $fell(Y) );
endmodule

module nand2_sva (input logic A,B, input logic Y);
  default clocking cb @ (A or B); endclocking

  assert property ( !$isunknown({A,B}) |-> ##0 (Y === ~(A & B)) );
  assert property ( !$isunknown({A,B}) |-> ##0 !$isunknown(Y) );

  genvar j;
  generate
    for (j = 0; j < 4; j++) begin : cov_vecs
      cover property ( ##0 ({A,B} == j[1:0]) );
    end
  endgenerate
  cover property ( ##0 $rose(Y) );
  cover property ( ##0 $fell(Y) );
endmodule

// Bind to DUTs
bind nand4 nand4_sva u_nand4_sva (
  .A(A), .B(B), .C(C), .D(D),
  .nand1_out(nand1_out), .nand2_out(nand2_out),
  .Y(Y)
);

bind nand2 nand2_sva u_nand2_sva (
  .A(A), .B(B), .Y(Y)
);