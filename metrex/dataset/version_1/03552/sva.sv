// SVA checkers for ripple_carry_adder and full_adder

module rca4_sva (
  input logic        clk,
  input logic [3:0]  A,
  input logic [3:0]  B,
  input logic        Cin,
  input logic [3:0]  S,
  input logic        Cout,
  input logic [3:0]  carry
);
  default clocking cb @(posedge clk); endclocking

  // No-X on outputs when inputs are known
  assert property (!$isunknown({A,B,Cin}) |-> !$isunknown({S,Cout,carry}))
    else $error("RCA: X/Z detected on outputs with clean inputs");

  // Whole-adder correctness
  assert property ({Cout,S} == A + B + Cin)
    else $error("RCA: {Cout,S} != A+B+Cin");

  // Bitwise sum/carry chain checks
  assert property (S[0]     == (A[0]^B[0]^Cin))
    else $error("RCA: S[0] mismatch");
  assert property (carry[0] == ((A[0]&B[0]) | (Cin & (A[0]^B[0]))))
    else $error("RCA: carry[0] mismatch");

  assert property (S[1]     == (A[1]^B[1]^carry[0]))
    else $error("RCA: S[1] mismatch");
  assert property (carry[1] == ((A[1]&B[1]) | (carry[0] & (A[1]^B[1]))))
    else $error("RCA: carry[1] mismatch");

  assert property (S[2]     == (A[2]^B[2]^carry[1]))
    else $error("RCA: S[2] mismatch");
  assert property (carry[2] == ((A[2]&B[2]) | (carry[1] & (A[2]^B[2]))))
    else $error("RCA: carry[2] mismatch");

  assert property (S[3]     == (A[3]^B[3]^carry[2]))
    else $error("RCA: S[3] mismatch");
  assert property (Cout     == ((A[3]&B[3]) | (carry[2] & (A[3]^B[3]))))
    else $error("RCA: Cout mismatch");

  // Targeted functional coverage
  cover property (A==4'h0 && B==4'h0 && Cin==1'b0 && S==4'h0 && Cout==1'b0);                 // zero add
  cover property (Cout==1'b1);                                                                // any overflow
  cover property (Cin==1'b1 && (A^B)==4'hF && (A&B)==4'h0 && Cout==1'b1);                     // full 4-bit propagate
  cover property (Cin==1'b1 && A[0]==1'b0 && B[0]==1'b0 && carry[0]==1'b0);                   // early kill at bit0
  cover property ((A[0]&B[0]) && (A[1]^B[1]) && (A[2]^B[2]) && (A[3]^B[3]) && !Cin && Cout);  // gen at bit0, ripple through
endmodule


module fa_sva (
  input logic clk,
  input logic A,
  input logic B,
  input logic Cin,
  input logic S,
  input logic Cout
);
  default clocking cb @(posedge clk); endclocking

  // Full-adder correctness (equivalent to both S and Cout equations)
  assert property ({Cout,S} == A + B + Cin)
    else $error("FA: {Cout,S} != A+B+Cin");

  // FA mode coverage: generate, propagate, kill
  cover property ((A&B) && (Cin==1'b0) && (Cout==1'b1));                          // generate
  cover property ((A^B) && !(A&B) && (Cin==1'b1) && (Cout==1'b1) && (S==1'b0));   // propagate with Cin=1
  cover property ((!A && !B) && (Cin==1'b1) && (Cout==1'b0) && (S==1'b1));        // kill with Cin=1
endmodule

// Example binds (connect a testbench clock):
// bind ripple_carry_adder rca4_sva rca4_chk(.clk(tb_clk), .A(A), .B(B), .Cin(Cin), .S(S), .Cout(Cout), .carry(carry));
// bind full_adder        fa_sva   fa_chk  (.clk(tb_clk), .A(A), .B(B), .Cin(Cin), .S(S), .Cout(Cout));