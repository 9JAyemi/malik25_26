module modulo_operator_sva (
  input logic [31:0] div,
  input logic [31:0] divisor,
  input logic [31:0] rem
);

  ///// Functional checks for modulo_operator /////
  // When divisor is zero, rem must be zero.
  check_zero_divisor_zero_rem: assert property (
    @(posedge $global_clock) (divisor == 32'd0) |-> (rem == 32'd0)
  );

  // When divisor is non-zero, rem equals div % divisor.
  check_mod_operation_correct: assert property (
    @(posedge $global_clock) (divisor != 32'd0) |-> (rem == (div % divisor))
  );

  // For non-zero divisor, remainder must be less than divisor.
  check_remainder_range: assert property (
    @(posedge $global_clock) (divisor != 32'd0) |-> (rem < divisor)
  );

  // If dividend is zero, remainder must be zero regardless of divisor.
  check_zero_dividend_zero_rem: assert property (
    @(posedge $global_clock) (div == 32'd0) |-> (rem == 32'd0)
  );

  // If divisor equals dividend, remainder must be zero.
  check_equal_div_divisor_zero_rem: assert property (
    @(posedge $global_clock) (divisor == div) |-> (rem == 32'd0)
  );

  // If divisor is greater than dividend, remainder equals dividend.
  check_divisor_greater_than_dividend: assert property (
    @(posedge $global_clock) (divisor > div) |-> (rem == div)
  );

  // If divisor is 1, remainder must be zero.
  check_divisor_one_zero_rem: assert property (
    @(posedge $global_clock) (divisor == 32'd1) |-> (rem == 32'd0)
  );

  // If divisor is 2, remainder equals LSB of dividend.
  check_divisor_two_lsb_rem: assert property (
    @(posedge $global_clock) (divisor == 32'd2) |-> (rem == {31'd0, div[0]})
  );

  // For power-of-two divisor, remainder equals div masked by (divisor-1).
  check_power_of_two_mask: assert property (
    @(posedge $global_clock) (divisor != 32'd0) && ((divisor & (divisor - 32'd1)) == 32'd0)
      |-> (rem == (div & (divisor - 32'd1)))
  );

endmodule