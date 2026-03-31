```systemverilog
module binary_counter_sva (
    input logic clk,
    input logic reset,
    input logic enable,
    output logic [3:0] count
);
    ///// Device reset /////
    // At reset assertion, the counter must be driven to 0.
    reset: assert property (
        @(posedge clk) reset |-> (count == 4'b0000)
    );

    ///// Enable control /////
    // The counter should only increment when enable is high.
    increment: assert property (
        @(posedge clk) disable iff (reset) (enable |-> count == count + 1)
    );

    // The counter should not increment when enable is low.
    no_increment: assert property (
        @(posedge clk) disable iff (reset) (!enable |-> count == count)
    );

    ///// Count range /////
    // The counter should not exceed 4'b1111.
    count_range: assert property (
        @(posedge clk) disable iff (reset) (count <= 4'b1111)
    );

    // The counter should not go below 4'b0000.
    count_non_negative: assert property (
        @(posedge clk) disable iff (reset) (count >= 4'b0000)
    );

    ///// Sequential logic /////
    // The counter should only change on the positive edge of the clock.
    sequential_logic: assert property (
        @(posedge clk) disable iff (reset) (count == count @ (posedge clk))
    );

    // The counter should not change when reset is high.
    no_change_on_reset: assert property (
        @(posedge clk) disable iff (!reset) (count == count @ (posedge clk))
    );

    // The counter should not change when both reset and enable are high.
    no_change_on_reset_and_enable: assert property (
        @(posedge clk) disable iff (!reset) (reset |-> count == count @ (posedge clk))
    );

    // The counter should not change when both reset and enable are low.
    no_change_on_reset_and_no_enable: assert property (
        @(posedge clk) disable iff (!reset) (!enable |-> count == count @ (posedge clk))
    );

    // The counter should not change when both reset and enable are high.
    no_change_on_enable_and_reset: assert property (
        @(posedge clk) disable iff (!reset) (enable |-> count == count @ (posedge clk))
    );

endmodule
```