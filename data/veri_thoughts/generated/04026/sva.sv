module comparator_sva #(
  parameter n = 8
) (
  input logic clk,
  input logic [n-1:0] num1,
  input logic [n-1:0] num2,
  input logic cmp_mode,
  input logic gt,
  input logic eq,
  input logic lt
);

  // In unsigned mode, gt matches the unsigned comparison.
  check_unsigned_gt: assert property (
    @(posedge clk) (cmp_mode === 1'b0) |-> (gt === (num1 > num2))
  );

  // In unsigned mode, eq matches the unsigned comparison.
  check_unsigned_eq: assert property (
    @(posedge clk) (cmp_mode === 1'b0) |-> (eq === (num1 == num2))
  );

  // In unsigned mode, lt matches the unsigned comparison.
  check_unsigned_lt: assert property (
    @(posedge clk) (cmp_mode === 1'b0) |-> (lt === (num1 < num2))
  );

  // In signed mode, gt matches the signed comparison.
  check_signed_gt: assert property (
    @(posedge clk) (cmp_mode === 1'b1) |-> (gt === ($signed(num1) > $signed(num2)))
  );

  // In signed mode, eq matches the signed comparison.
  check_signed_eq: assert property (
    @(posedge clk) (cmp_mode === 1'b1) |-> (eq === ($signed(num1) == $signed(num2)))
  );

  // In signed mode, lt matches the signed comparison.
  check_signed_lt: assert property (
    @(posedge clk) (cmp_mode === 1'b1) |-> (lt === ($signed(num1) < $signed(num2)))
  );

  // Equality is independent of comparison mode.
  check_eq_mode_independent: assert property (
    @(posedge clk) (eq === (num1 == num2))
  );

  // Exactly one comparison result is asserted.
  check_results_complete_and_exclusive: assert property (
    @(posedge clk) ((gt || eq || lt) && !(gt && eq) && !(gt && lt) && !(eq && lt))
  );

  // Equal inputs produce only the equality result.
  check_equal_inputs_select_eq_only: assert property (
    @(posedge clk) (num1 == num2) |-> (eq && !gt && !lt)
  );

endmodule