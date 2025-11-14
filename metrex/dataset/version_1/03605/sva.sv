// SVA for adder: sum must be (A+B) mod 16, zero-extended to 5 bits.
// Bindable assertions and coverage.

module adder_sva (
  input logic [3:0] A, B,
  input logic [4:0] sum
);

  // Functional equivalence: zero-delay after any input change
  property p_masked_sum;
    @(A or B) disable iff ($isunknown({A,B}))
      ##0 (sum == {1'b0, (A+B)[3:0]});
  endproperty
  assert property (p_masked_sum)
    else $error("adder: sum != zero-extended (A+B)%%16");

  // Range/MSB check (redundant but clear intent)
  property p_msb_zero;
    @(A or B) disable iff ($isunknown({A,B}))
      ##0 (sum[4] == 1'b0);
  endproperty
  assert property (p_msb_zero)
    else $error("adder: sum[4] must be 0");

  // Coverage: exercise both paths and key corners
  cover property (@(A or B) disable iff ($isunknown({A,B})) ##0 ((A+B)[4] == 1'b0)); // no overflow
  cover property (@(A or B) disable iff ($isunknown({A,B})) ##0 ((A+B)[4] == 1'b1)); // overflow
  cover property (@(A or B) disable iff ($isunknown({A,B})) ##0 ((A==4'h0 && B==4'h0) && sum==5'd0));
  cover property (@(A or B) disable iff ($isunknown({A,B})) ##0 ((A==4'hF && B==4'hF) && sum==5'd14));
  cover property (@(A or B) disable iff ($isunknown({A,B})) ##0 (((A+B)==5'd16) && sum==5'd0));
  cover property (@(A or B) disable iff ($isunknown({A,B})) ##0 (A==4'hF && B==4'h1 && sum==5'd0));
  cover property (@(A or B) disable iff ($isunknown({A,B})) ##0 (A==4'h1 && B==4'hF && sum==5'd0));

endmodule

// Bind into DUT
bind adder adder_sva i_adder_sva (.A(A), .B(B), .sum(sum));