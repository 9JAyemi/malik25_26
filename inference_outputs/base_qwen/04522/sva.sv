```systemverilog
module binary_counter_sva (
  input logic clk,
  input logic reset,
  output logic [3:0] count
);
  // Reset behavior: count should be 0 after reset
  reset_behavior: assert property (
    @(posedge clk) disable iff (!reset) count == 4'b0000
  );

  // Count should increment by 1 on each clock cycle when not reset
  count_increment: assert property (
    @(posedge clk) disable iff (!reset) (count != 4'b1111) |-> count + 4'b0001 == count
  );

  // Count should wrap around to 0 when it reaches 15
  count_wraparound: assert property (
    @(posedge clk) disable iff (!reset) count == 4'b1111 |-> count + 4'b0001 == 4'b0000
  );

  // Count should not change when reset is asserted
  count_stable_on_reset: assert property (
    @(posedge clk) disable iff (!reset) reset |-> count == count
  );

  // Count should not increment when reset is asserted
  count_no_increment_on_reset: assert property (
    @(posedge clk) disable iff (!reset) reset |-> count + 4'b0001 == count
  );

  // Count should not wrap around when reset is asserted
  count_no_wraparound_on_reset: assert property (
    @(posedge clk) disable iff (!reset) reset |-> count == count
  );

  // Count should not change when count is at its maximum value
  count_stable_at_max: assert property (
    @(posedge clk) disable iff (!reset) count == 4'b1111 |-> count == count
  );

  // Count should not increment when count is at its maximum value
  count_no_increment_at_max: assert property (
    @(posedge clk) disable iff (!reset) count == 4'b1111 |-> count + 4'b0001 == count
  );

  // Count should not wrap around when count is at its maximum value
  count_no_wraparound_at_max: assert property (
    @(posedge clk) disable iff (!reset) count == 4'b1111 |-> count == count
  );
endmodule
```