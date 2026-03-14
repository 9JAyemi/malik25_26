module modulo_operator_sva (
  input logic clk,
  input logic reset_n,
  input logic [31:0] dividend,
  input logic [31:0] divisor,
  input logic [31:0] remainder
);
  // If divisor is 0, remainder must be 0.
  check_div_by_zero_zero: assert property (
    @(posedge clk) disable iff (!reset_n) (divisor == 32'd0) |-> (remainder == 32'd0)
  );

  // For known nonzero divisor, remainder equals dividend % divisor.
  check_exact_modulo_result: assert property (
    @(posedge clk) disable iff (!reset_n) (!$isunknown(dividend) && !$isunknown(divisor) && (divisor != 32'd0)) |-> (remainder == (dividend % divisor))
  );

  // For known nonzero divisor, remainder is less than divisor.
  check_remainder_range: assert property (
    @(posedge clk) disable iff (!reset_n) (!$isunknown({dividend, divisor}) && (divisor != 32'd0)) |-> (remainder < divisor)
  );

  // If dividend < divisor and divisor != 0, remainder equals dividend.
  check_remainder_eq_dividend_when_smaller: assert property (
    @(posedge clk) disable iff (!reset_n) (!$isunknown({dividend, divisor}) && (divisor != 32'd0) && (dividend < divisor)) |-> (remainder == dividend)
  );

  // If dividend == divisor != 0, remainder is 0.
  check_remainder_zero_when_equal: assert property (
    @(posedge clk) disable iff (!reset_n) (!$isunknown({dividend, divisor}) && (divisor != 32'd0) && (dividend == divisor)) |-> (remainder == 32'd0)
  );

  // If divisor == 1, remainder is 0.
  check_remainder_zero_divisor_one: assert property (
    @(posedge clk) disable iff (!reset_n) (divisor == 32'd1) |-> (remainder == 32'd0)
  );

  // If divisor == 2, remainder equals LSB of dividend.
  check_remainder_parity_divisor_two: assert property (
    @(posedge clk) disable iff (!reset_n) (!$isunknown({dividend, divisor}) && (divisor == 32'd2)) |-> ((remainder[0] == dividend[0]) && (remainder[31:1] == 31'd0))
  );

  // Output must be stable if inputs are stable (purely combinational).
  check_stable_when_inputs_stable: assert property (
    @(posedge clk) disable iff (!reset_n) ($stable(dividend) && $stable(divisor)) |-> $stable(remainder)
  );

  // If dividend is 0, remainder is 0.
  check_remainder_zero_when_dividend_zero: assert property (
    @(posedge clk) disable iff (!reset_n) (!$isunknown(divisor) && (dividend == 32'd0)) |-> (remainder == 32'd0)
  );

  // For known nonzero divisor, (dividend - remainder) is divisible by divisor.
  check_difference_divisible: assert property (
    @(posedge clk) disable iff (!reset_n) (!$isunknown({dividend, divisor, remainder}) && (divisor != 32'd0)) |-> (((dividend - remainder) % divisor) == 32'd0)
  );

  // For known nonzero divisor, remainder is not greater than dividend.
  check_remainder_le_dividend: assert property (
    @(posedge clk) disable iff (!reset_n) (!$isunknown({dividend, divisor}) && (divisor != 32'd0)) |-> (remainder <= dividend)
  );
endmodule