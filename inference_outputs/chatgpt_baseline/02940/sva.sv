module add_sub_sva (
  input logic clk,
  input logic reset,
  input logic operation,
  input logic [3:0] A,
  input logic [3:0] B,
  input logic [3:0] result
);

  // While reset is LOW, result must be zero.
  reset_level_forces_zero: assert property (
    @(posedge clk) (reset == 1'b0) |-> (result == 4'b0000)
  );

  // On the first clock after reset deasserts (LOW->HIGH), result is still zero.
  first_clk_after_reset_release_zero: assert property (
    @(posedge clk) (reset == 1'b1) && ($past(reset) == 1'b0) |-> (result == 4'b0000)
  );

  // With op=0, next result is (A+B) LSBs from the previous cycle.
  update_sum_when_op0: assert property (
    @(posedge clk) disable iff (!reset)
      $past(reset) && ($past(operation) == 1'b0)
      |-> (result == (($past(A) + $past(B)) & 4'hF))
  );

  // With op=1, next result is (A-B) LSBs from the previous cycle.
  update_diff_when_op1: assert property (
    @(posedge clk) disable iff (!reset)
      $past(reset) && ($past(operation) == 1'b1)
      |-> (result == (($past(A) - $past(B)) & 4'hF))
  );

endmodule