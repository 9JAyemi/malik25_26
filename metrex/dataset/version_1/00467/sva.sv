// SVA checker for binary_adder
// Bind this to the DUT; no clock required (uses input-change event).
module binary_adder_sva (
  input  logic [3:0] A,
  input  logic [3:0] B,
  input  logic       Cin,
  input  logic [3:0] Sum,
  input  logic       Cout
);
  // Trigger assertions/coverage whenever inputs change
  event comb_ev;
  always @(A or B or Cin) -> comb_ev;

  // Expected 5-bit result
  logic [4:0] exp;
  always_comb exp = A + B + Cin;

  // Sanity: no X/Z on outputs when inputs are known
  a_no_x_inputs:      assert property (@(comb_ev) !$isunknown({A,B,Cin}));
  a_no_x_outputs:     assert property (@(comb_ev) (!$isunknown({A,B,Cin})) |-> (!$isunknown({Sum,Cout})));

  // Functional correctness (golden spec)
  a_add_correct:      assert property (@(comb_ev) {Cout, Sum} == exp);

  // Helpful local checks to catch width/bit-wiring issues
  a_lsb_sum:          assert property (@(comb_ev) Sum[0]  == (A[0] ^ B[0] ^ Cin));
  a_zero_identity:    assert property (@(comb_ev) (B==4'h0 && Cin==1'b0) |-> (Sum==A && Cout==1'b0));
  a_comm_identity:    assert property (@(comb_ev) (A==4'h0 && Cin==1'b0) |-> (Sum==B && Cout==1'b0));

  // Coverage: key scenarios
  c_zero:             cover  property (@(comb_ev) (A==4'h0 && B==4'h0 && Cin==1'b0));
  c_overflow:         cover  property (@(comb_ev) (A==4'hF && B==4'hF && Cin==1'b1 && Cout==1'b1));
  c_full_propagate:   cover  property (@(comb_ev) (A==4'hF && B==4'h0 && Cin==1'b1 && {Cout,Sum}==5'h10));
  c_msbit_generate:   cover  property (@(comb_ev) (A[3] && B[3] && !Cin && Cout));

endmodule

// Bind into the DUT type (connects to instance internals by name)
bind binary_adder binary_adder_sva sva(
  .A(A), .B(B), .Cin(Cin), .Sum(Sum), .Cout(Cout)
);