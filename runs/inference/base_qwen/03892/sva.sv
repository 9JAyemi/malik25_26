module bin_counter_sva (
  input logic clk,
  input logic reset,
  input logic enable,
  output logic [3:0] count
);
  ///// Device reset /////
  // At reset assertion, the counter must be driven to 0.
  reset: assert property (
    @(posedge clk) disable iff (!reset) (reset |-> count == 4'b0)
  );

  ///// Enable control /////
  // The counter can only increment when enable is high.
  increment_enable: assert property (
    @(posedge clk) disable iff (!reset) (enable |-> count == count + 1)
  );

  // The counter should not increment when enable is low.
  no_increment_disable: assert property (
    @(posedge clk) disable iff (!reset) (!enable |-> count == count)
  );

  ///// Count range /////
  // The counter should not exceed 4'b1111.
  count_range: assert property (
    @(posedge clk) disable iff (!reset) (count <= 4'b1111)
  );

  // The counter should not go below 4'b0000.
  count_non_negative: assert property (
    @(posedge clk) disable iff (!reset) (count >= 4'b0000)
  );

  ///// Sequential logic /////
  // The counter should only change on the positive edge of the clock.
  sequential_logic: assert property (
    @(posedge clk) disable iff (!reset) (count == count @ (posedge clk))
  );

  // The counter should not change when reset is high.
  no_change_on_reset: assert property (
    @(posedge clk) disable iff (!reset) (reset |-> count == count @ (posedge clk))
  );

  // The counter should not change when both reset and enable are low.
  no_change_on_reset_and_disable: assert property (
    @(posedge clk) disable iff (!reset) (!reset && !enable |-> count == count @ (posedge clk))
  );

  // The counter should increment on the positive edge of the clock when enable is high.
  increment_on_clk: assert property (
    @(posedge clk) disable iff (!reset) (enable |-> count == count @ (posedge clk) + 1)
  );

  // The counter should not increment on the positive edge of the clock when enable is low.
  no_increment_on_clk: assert property (
    @(posedge clk) disable iff (!reset) (!enable |-> count == count @ (posedge clk))
  );
endmodule