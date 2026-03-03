// SVA checkers for rippleCarryAdder and fullAdder.
// Bind these in your testbench and provide a sampling clock/reset.

module rca_asserts (
  input logic        clk,
  input logic        rst_n,
  input logic [3:0]  A,
  input logic [3:0]  B,
  input logic        Cin,
  input logic [3:0]  Sum,
  input logic        Cout
);
  default clocking cb @(posedge clk); endclocking

  // helpers
  let maj3(a,b,c) = (a & b) | (b & c) | (c & a);
  let c0 = maj3(A[0], B[0], Cin);
  let s0 = A[0] ^ B[0] ^ Cin;
  let c1 = maj3(A[1], B[1], c0);
  let s1 = A[1] ^ B[1] ^ c0;
  let c2 = maj3(A[2], B[2], c1);
  let s2 = A[2] ^ B[2] ^ c1;
  let c3 = maj3(A[3], B[3], c2);
  let s3 = A[3] ^ B[3] ^ c2;

  // arithmetic equivalence (width-safe)
  assert property (disable iff (!rst_n)
    {Cout, Sum} == ({1'b0, A} + {1'b0, B} + Cin)
  );

  // bitwise ripple correctness
  assert property (disable iff (!rst_n)
    (Sum[0]==s0) && (Sum[1]==s1) && (Sum[2]==s2) && (Sum[3]==s3) && (Cout==c3)
  );

  // no X on outputs when inputs are 0/1
  assert property (disable iff (!rst_n)
    !$isunknown({A,B,Cin}) |-> !$isunknown({Sum,Cout})
  );

  // pure combinational determinism (no memory)
  assert property (disable iff (!rst_n)
    {A,B,Cin} == $past({A,B,Cin}) |-> {Sum,Cout} == $past({Sum,Cout})
  );

  // Coverage: carry-out 0/1, propagate chain, generate/kill at LSB
  cover property (disable iff (!rst_n) Cout);
  cover property (disable iff (!rst_n) !Cout);
  cover property (disable iff (!rst_n) (&(A ^ B)) && Cin && Cout);            // full propagate chain
  cover property (disable iff (!rst_n) (A[0] & B[0]) && !Cin && c0);          // generate at bit0
  cover property (disable iff (!rst_n) !A[0] && !B[0] && Cin && !c0);         // kill at bit0

endmodule


module fa_asserts (
  input logic clk,
  input logic rst_n,
  input logic A,
  input logic B,
  input logic Cin,
  input logic Sum,
  input logic Cout
);
  default clocking cb @(posedge clk); endclocking

  // truth-function checks
  assert property (disable iff (!rst_n) Sum  == (A ^ B ^ Cin));
  assert property (disable iff (!rst_n) Cout == ((A & B) | (B & Cin) | (Cin & A)));

  // arithmetic width-safe check
  assert property (disable iff (!rst_n)
    {Cout, Sum} == ({1'b0, A} + {1'b0, B} + Cin)
  );

  // no X on outputs when inputs are 0/1
  assert property (disable iff (!rst_n)
    !$isunknown({A,B,Cin}) |-> !$isunknown({Sum,Cout})
  );

  // full input truth table coverage (all 8 minterms)
  cover property (disable iff (!rst_n) {A,B,Cin} == 3'b000);
  cover property (disable iff (!rst_n) {A,B,Cin} == 3'b001);
  cover property (disable iff (!rst_n) {A,B,Cin} == 3'b010);
  cover property (disable iff (!rst_n) {A,B,Cin} == 3'b011);
  cover property (disable iff (!rst_n) {A,B,Cin} == 3'b100);
  cover property (disable iff (!rst_n) {A,B,Cin} == 3'b101);
  cover property (disable iff (!rst_n) {A,B,Cin} == 3'b110);
  cover property (disable iff (!rst_n) {A,B,Cin} == 3'b111);
endmodule


// Example bind statements (hook clk/rst_n from your TB):
// bind rippleCarryAdder rca_asserts u_rca_asserts(.clk(tb_clk), .rst_n(tb_rst_n), .A(A), .B(B), .Cin(Cin), .Sum(Sum), .Cout(Cout));
// bind fullAdder       fa_asserts  u_fa_asserts (.clk(tb_clk), .rst_n(tb_rst_n), .A(A), .B(B), .Cin(Cin), .Sum(Sum), .Cout(Cout));