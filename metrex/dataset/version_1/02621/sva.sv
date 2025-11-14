// SVA for barrel_shifter (combinational, clockless checks)
// Bind these assertions to the DUT.

module barrel_shifter_sva (
  input  logic [3:0] A,
  input  logic [3:0] B,
  input  logic [3:0] result
);

  // Golden model for this DUT (given unsigned B, else-branch is unreachable)
  function automatic logic [3:0] model_res (logic [3:0] a, logic [3:0] b);
    if (b >= 4) model_res = 4'b0;
    else        model_res = a << b;
  endfunction

  // Functional equivalence when inputs are known
  property p_func_equiv;
    @(*) (!$isunknown({A,B})) |-> ##0 (result == model_res(A,B));
  endproperty
  assert property (p_func_equiv);

  // No X/Z on output when inputs are 0/1 only
  property p_no_x_out_when_inputs_known;
    @(*) (!$isunknown({A,B})) |-> ##0 (!$isunknown(result));
  endproperty
  assert property (p_no_x_out_when_inputs_known);

  // Key corner cases (under known inputs)
  assert property (@(*) (!$isunknown({A,B})) && (B==0) |-> ##0 (result==A));
  assert property (@(*) (!$isunknown({A,B})) && (B>=4) |-> ##0 (result==4'b0));
  assert property (@(*) (!$isunknown({A,B})) && (A==4'b0) |-> ##0 (result==4'b0));

  // Minimal but meaningful coverage of shift amounts and data patterns
  cover property (@(*) (!$isunknown({A,B})) && (B==0));
  cover property (@(*) (!$isunknown({A,B})) && (B==1));
  cover property (@(*) (!$isunknown({A,B})) && (B==2));
  cover property (@(*) (!$isunknown({A,B})) && (B==3));
  cover property (@(*) (!$isunknown({A,B})) && (B>=4));

  cover property (@(*) (!$isunknown({A,B})) && (A==4'h0));
  cover property (@(*) (!$isunknown({A,B})) && (A==4'hF));
  cover property (@(*) (!$isunknown({A,B})) && (A==4'hA)); // mixed pattern

endmodule

bind barrel_shifter barrel_shifter_sva bs_sva (.A(A), .B(B), .result(result));