```systemverilog
module binary_counter_sva (
    input logic clk,
    input logic reset,
    input logic enable,
    output logic [3:0] q
);
    ///// Device reset /////
    // At reset assertion, the counter must be driven to 0.
    reset: assert property (
        @(posedge clk) disable iff (!reset) (q == 4'b0000)
    );

    ///// Enable control /////
    // The counter can only increment when enable is high.
    increment: assert property (
        @(posedge clk) disable iff (!reset) (enable |-> q == q + 1)
    );

    // The counter should not increment when enable is low.
    no_increment: assert property (
        @(posedge clk) disable iff (!reset) (!enable |-> q == q)
    );

    ///// Counter range /////
    // The counter should not exceed 15.
    counter_range: assert property (
        @(posedge clk) disable iff (!reset) (q <= 4'b1111)
    );

    // The counter should not go below 0.
    counter_non_negative: assert property (
        @(posedge clk) disable iff (!reset) (q >= 4'b0000)
    );

    ///// Sequential logic /////
    // The counter should only change on the rising edge of the clock.
    sequential_logic: assert property (
        @(posedge clk) disable iff (!reset) (q == q @ (posedge clk))
    );

    // The counter should not change when reset is high.
    no_change_on_reset: assert property (
        @(posedge clk) disable iff (!reset) (reset |-> q == q @ (posedge clk))
    );

    // The counter should not change when both reset and enable are high.
    no_change_on_reset_and_enable: assert property (
        @(posedge clk) disable iff (!reset) (reset && enable |-> q == q @ (posedge clk))
    );

    // The counter should not change when both reset and enable are low.
    no_change_on_reset_and_no_enable: assert property (
        @(posedge clk) disable iff (!reset) (!reset && !enable |-> q == q @ (posedge clk))
    );

    // The counter should not change when only enable is low.
    no_change_on_no_enable: assert property (
        @(posedge clk) disable iff (!reset) (!enable |-> q == q @ (posedge clk))
    );
endmodule
```