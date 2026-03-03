// SVA for four_bit_adder and full_adder (combinational; sample after ##0 to avoid delta glitches)

module four_bit_adder_sva
(
  input  logic [3:0] A,
  input  logic [3:0] B,
  input  logic       Cin,
  input  logic [3:0] S,
  input  logic       Cout
);
  // Local combinational reference model
  let c0 = (A[0]&B[0]) | (A[0]&Cin) | (B[0]&Cin);
  let s0 = A[0]^B[0]^Cin;
  let c1 = (A[1]&B[1]) | (A[1]&c0)  | (B[1]&c0);
  let s1 = A[1]^B[1]^c0;
  let c2 = (A[2]&B[2]) | (A[2]&c1)  | (B[2]&c1);
  let s2 = A[2]^B[2]^c1;
  let c3 = (A[3]&B[3]) | (A[3]&c2)  | (B[3]&c2);
  let s3 = A[3]^B[3]^c2;

  // Vector-accurate arithmetic
  property p_sumvec; @(A or B or Cin) ##0 {Cout,S} == A + B + Cin; endproperty
  assert property (p_sumvec);

  // Bitwise ripple correctness
  property p_bitwise; @(A or B or Cin) ##0 (S == {s3,s2,s1,s0}) && (Cout == c3); endproperty
  assert property (p_bitwise);

  // No X/Z on outputs when inputs are known
  property p_no_x; @(A or B or Cin or S or Cout) (!$isunknown({A,B,Cin})) |-> ##0 !$isunknown({S,Cout}); endproperty
  assert property (p_no_x);

  // Concise functional coverage
  cover property (@(A or B or Cin) ##0 (Cout==0));                            // no carry out
  cover property (@(A or B or Cin) ##0 (Cout==1));                            // carry out
  cover property (@(A or B or Cin) ##0 ((A^B)==4'hF && Cin==1 && Cout==1));   // full propagate chain
  cover property (@(A or B or Cin) ##0 ({Cout,S}==5'h00));                    // sum zero
  cover property (@(A or B or Cin) ##0 ({Cout,S}==5'h1F));                    // max sum
endmodule

module full_adder_sva
(
  input  logic A,
  input  logic B,
  input  logic Cin,
  input  logic S,
  input  logic C
);
  // Functional correctness
  property p_fa_func; @(A or B or Cin) ##0 (S == (A^B^Cin)) && (C == ((A&B)|(A&Cin)|(B&Cin))); endproperty
  assert property (p_fa_func);

  // No X/Z on outputs when inputs are known
  property p_fa_no_x; @(A or B or Cin or S or C) (!$isunknown({A,B,Cin})) |-> ##0 !$isunknown({S,C}); endproperty
  assert property (p_fa_no_x);

  // Coverage of key FA behaviors
  cover property (@(A or B or Cin) ##0 ((A^B) && !Cin && (C==0) && (S==1))); // propagate, Cin=0
  cover property (@(A or B or Cin) ##0 ((A^B) &&  Cin && (C==1) && (S==0))); // propagate, Cin=1
  cover property (@(A or B or Cin) ##0 ((A&B) && (C==1)));                   // generate
endmodule

// Bind SVA to DUTs
bind four_bit_adder four_bit_adder_sva u_four_bit_adder_sva(.A(A),.B(B),.Cin(Cin),.S(S),.Cout(Cout));
bind full_adder     full_adder_sva     u_full_adder_sva    (.A(A),.B(B),.Cin(Cin),.S(S),.C(C));