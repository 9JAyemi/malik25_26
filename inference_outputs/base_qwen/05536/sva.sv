```systemverilog
module up_down_counter_sva (
    input logic clk,
    input logic reset,
    input logic up_down,
    input logic load,
    input logic [3:0] data_in,
    output logic [3:0] count
);
    ///// Device reset /////
    // At reset assertion, a device must drive count LOW.
    reset: assert property (
        @(posedge clk) reset |-> (count == 4'b0)
    );

    ///// Load behavior /////
    // When load is asserted, count should be driven by data_in.
    load_behavior: assert property (
        @(posedge clk) disable iff (reset) load |-> (count == data_in)
    );

    ///// Up/Down behavior /////
    // When up_down is asserted, count should increment.
    up_behavior: assert property (
        @(posedge clk) disable iff (reset) up_down |-> (count == count + 1)
    );

    // When up_down is deasserted, count should decrement.
    down_behavior: assert property (
        @(posedge clk) disable iff (reset) !up_down |-> (count == count - 1)
    );

    ///// Sequential logic /////
    // Count should not change when neither load nor up_down is asserted.
    no_change: assert property (
        @(posedge clk) disable iff (reset) !(load | up_down) |-> (count == count)
    );

endmodule
```