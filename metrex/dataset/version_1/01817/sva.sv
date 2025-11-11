// SVA checkers for full_adder, half_adder, four_bit_adder
// Bind these into the DUTs to verify function and cover key cases.

////////////////////////////////////////////////////////////
// Full Adder SVA
module full_adder_sva (
  input logic A, B, Cin, S, Cout,
  input logic w1, w2, w3
);
  default clocking cb @(
    posedge A or negedge A or
    posedge B or negedge B or
    posedge Cin or negedge Cin
  ); endclocking

  // Functional correctness (guard X/Z on inputs)
  ap_func: assert property (
    !$isunknown({A,B,Cin}) |-> ##0
      (S == (A ^ B ^ Cin) &&
       Cout == ((A & B) | ((A ^ B) & Cin)))
  );

  // Structural wire checks
  ap_struct: assert property (
    !$isunknown({A,B,Cin}) |-> ##0
      (w1 == (A ^ B)) &&
      (w2 == (A & B)) &&
      (w3 == ((A ^ B) & Cin))
  );

  // No X/Z on outputs when inputs known
  ap_no_x: assert property (
    !$isunknown({A,B,Cin}) |-> ##0
      !$isunknown({S,Cout,w1,w2,w3})
  );

  // Truth-table coverage (8 combos)
  cover property ({A,B,Cin} == 3'b000);
  cover property ({A,B,Cin} == 3'b001);
  cover property ({A,B,Cin} == 3'b010);
  cover property ({A,B,Cin} == 3'b011);
  cover property ({A,B,Cin} == 3'b100);
  cover property ({A,B,Cin} == 3'b101);
  cover property ({A,B,Cin} == 3'b110);
  cover property ({A,B,Cin} == 3'b111);
  // Output coverage
  cover property (S == 1'b0);
  cover property (S == 1'b1);
  cover property (Cout == 1'b0);
  cover property (Cout == 1'b1);
endmodule

bind full_adder full_adder_sva
  (.A(A), .B(B), .Cin(Cin), .S(S), .Cout(Cout), .w1(w1), .w2(w2), .w3(w3));


////////////////////////////////////////////////////////////
// Half Adder SVA
module half_adder_sva (
  input logic A, B, S, Cout
);
  default clocking cb @(
    posedge A or negedge A or
    posedge B or negedge B
  ); endclocking

  ap_func: assert property (
    !$isunknown({A,B}) |-> ##0
      (S == (A ^ B) && Cout == (A & B))
  );

  ap_no_x: assert property (
    !$isunknown({A,B}) |-> ##0
      !$isunknown({S,Cout})
  );

  // Truth-table coverage (4 combos)
  cover property ({A,B} == 2'b00);
  cover property ({A,B} == 2'b01);
  cover property ({A,B} == 2'b10);
  cover property ({A,B} == 2'b11);
  cover property (S == 1'b0);
  cover property (S == 1'b1);
  cover property (Cout == 1'b0);
  cover property (Cout == 1'b1);
endmodule

bind half_adder half_adder_sva
  (.A(A), .B(B), .S(S), .Cout(Cout));


////////////////////////////////////////////////////////////
// 4-bit Ripple-Carry Adder SVA
module four_bit_adder_sva (
  input  logic [3:0] A, B,
  input  logic       Cin,
  input  logic [3:0] S,
  input  logic       Cout,
  input  logic       c1, c2, c3
);
  // Trigger on any input bit toggle
  default clocking cb @(
    posedge Cin or negedge Cin or
    posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or
    posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or
    posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or
    posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3]
  ); endclocking

  // Top-level correctness
  ap_sum: assert property (
    !$isunknown({A,B,Cin}) |-> ##0
      ({Cout,S} == (A + B + Cin))
  );

  // Internal ripple carries correctness
  ap_c1: assert property (
    !$isunknown({A[0],B[0],Cin}) |-> ##0
      (c1 == ((A[0] & B[0]) | ((A[0] ^ B[0]) & Cin)))
  );
  ap_c2: assert property (
    !$isunknown({A[1],B[1],c1}) |-> ##0
      (c2 == ((A[1] & B[1]) | ((A[1] ^ B[1]) & c1)))
  );
  ap_c3: assert property (
    !$isunknown({A[2],B[2],c2}) |-> ##0
      (c3 == ((A[2] & B[2]) | ((A[2] ^ B[2]) & c2)))
  );

  // No X/Z on outputs when inputs known
  ap_no_x: assert property (
    !$isunknown({A,B,Cin}) |-> ##0
      !$isunknown({S,Cout,c1,c2,c3})
  );

  // Key scenario coverage
  cover property ({A,B,Cin} == {4'h0,4'h0,1'b0}); // all zero
  cover property ({A,B,Cin} == {4'hF,4'hF,1'b1}); // max + max + 1 -> overflow
  cover property ({A,B,Cin} == {4'b0111,4'b0001,1'b0}); // long propagate chain
  cover property (Cout == 1'b0);
  cover property (Cout == 1'b1);
endmodule

bind four_bit_adder four_bit_adder_sva
  (.A(A), .B(B), .Cin(Cin), .S(S), .Cout(Cout), .c1(c1), .c2(c2), .c3(c3));