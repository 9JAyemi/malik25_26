// SVA checker for csa_generate_adder_32bit
// Binds to DUT and checks functional equivalence and key corner cases.

`ifndef SYNTHESIS
module csa_generate_adder_32bit_sva #(parameter int SIZE = 32)
(
  input logic [SIZE-1:0] A,
  input logic [SIZE-1:0] B,
  input logic [SIZE-1:0] S,
  input logic            C_OUT
);

  // Full unsigned sum helper
  function automatic logic [SIZE:0] uadd(input logic [SIZE-1:0] x, y);
    return {1'b0, x} + {1'b0, y};
  endfunction

  // Core: sum and carry-out must match unsigned addition (no carry-in)
  property p_sum_ok;
    @(A or B)
      !$isunknown({A,B}) |-> ##0 {C_OUT, S} == uadd(A,B);
  endproperty
  assert property (p_sum_ok);

  // X-propagation: known inputs must produce known outputs
  property p_no_x_on_outputs;
    @(A or B)
      !$isunknown({A,B}) |-> ##0 !$isunknown({S,C_OUT});
  endproperty
  assert property (p_no_x_on_outputs);

  // Redundant unsigned identity: carry-out equals wrap-around detection
  property p_carry_wrap_equiv;
    @(A or B)
      !$isunknown({A,B}) |-> ##0 (C_OUT == ((S < A) || (S < B)));
  endproperty
  assert property (p_carry_wrap_equiv);

  // Coverage: no-carry and carry cases
  cover property (@(A or B) ##0 (uadd(A,B)[SIZE] == 1'b0));
  cover property (@(A or B) ##0 (uadd(A,B)[SIZE] == 1'b1));

  // Coverage: trivial and overflow corners
  cover property (@(A or B) (A == '0 && B == '0));
  cover property (@(A or B) (A == {SIZE{1'b1}} && B == {{(SIZE-1){1'b0}},1'b1}));

  // Coverage: observe C_OUT asserted at least once
  cover property (@(A or B) ##0 C_OUT);

endmodule

bind csa_generate_adder_32bit csa_generate_adder_32bit_sva #(.SIZE(SIZE))
  csa_generate_adder_32bit_sva_i (.*);
`endif