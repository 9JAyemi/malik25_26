// SVA for adder4 and full_adder
// Bind these checkers to the DUTs

module adder4_sva (
  input [3:0] A,
  input [3:0] B,
  input       Cin,
  input [3:0] Sum,
  input       Cout
);
  // Functional correctness of 4-bit ripple adder
  property p_add_correct;
    @(A or B or Cin) ##0 {Cout, Sum} == (A + B + Cin);
  endproperty
  assert property (p_add_correct);

  // No X/Z on outputs when inputs are clean
  property p_no_x_out;
    @(A or B or Cin or Sum or Cout)
      !$isunknown({A,B,Cin}) |-> ##0 !$isunknown({Sum,Cout});
  endproperty
  assert property (p_no_x_out);

  // Bitwise check against expected carry chain
  logic [4:0] exp_carry;
  always_comb begin
    exp_carry[0] = Cin;
    for (int i = 0; i < 4; i++) begin
      exp_carry[i+1] = (A[i] & B[i]) | (A[i] & exp_carry[i]) | (B[i] & exp_carry[i]);
    end
  end
  property p_chain_bits;
    @(A or B or Cin)
      ##0 (Sum[0] == (A[0]^B[0]^exp_carry[0])) &&
          (Sum[1] == (A[1]^B[1]^exp_carry[1])) &&
          (Sum[2] == (A[2]^B[2]^exp_carry[2])) &&
          (Sum[3] == (A[3]^B[3]^exp_carry[3])) &&
          (Cout    == exp_carry[4]);
  endproperty
  assert property (p_chain_bits);

  // Useful corner-case coverage
  cover property (@(A or B or Cin) ##0 {Cout,Sum} == 5'd0);
  cover property (@(A or B or Cin) ##0 Cout == 1'b1);                       // overflow seen
  cover property (@(A or B or Cin) ##0 Sum == 4'hF && Cout == 1'b0);        // max sum without carry
  cover property (@(A or B or Cin) ##0 A==4'hF && B==4'h0 && Cin && Cout);  // full propagate chain
  cover property (@(A or B or Cin) ##0 A==B && !Cin);                        // equal operands, Cin=0
  cover property (@(A or B or Cin) ##0 A==B &&  Cin);                        // equal operands, Cin=1
endmodule


module full_adder_sva (
  input a,
  input b,
  input cin,
  input sum,
  input cout
);
  // Functional correctness of 1-bit full adder
  property p_fa_add;
    @(a or b or cin) ##0 {cout, sum} == (a + b + cin);
  endproperty
  assert property (p_fa_add);

  // No X/Z on outputs when inputs are clean
  property p_fa_no_x_out;
    @(a or b or cin or sum or cout)
      !$isunknown({a,b,cin}) |-> ##0 !$isunknown({sum,cout});
  endproperty
  assert property (p_fa_no_x_out);

  // Cover all input combinations
  cover property (@(a or b or cin) ##0 {a,b,cin} == 3'b000);
  cover property (@(a or b or cin) ##0 {a,b,cin} == 3'b001);
  cover property (@(a or b or cin) ##0 {a,b,cin} == 3'b010);
  cover property (@(a or b or cin) ##0 {a,b,cin} == 3'b011);
  cover property (@(a or b or cin) ##0 {a,b,cin} == 3'b100);
  cover property (@(a or b or cin) ##0 {a,b,cin} == 3'b101);
  cover property (@(a or b or cin) ##0 {a,b,cin} == 3'b110);
  cover property (@(a or b or cin) ##0 {a,b,cin} == 3'b111);
endmodule


bind adder4     adder4_sva      sva_adder4     (.*);
bind full_adder full_adder_sva  sva_fulladder  (.*);