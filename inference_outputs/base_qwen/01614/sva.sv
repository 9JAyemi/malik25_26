```systemverilog
module up_down_counter_sva (
    input logic clk,
    input logic load,
    input logic up_down,
    input logic [3:0] input_data,
    output logic [3:0] Q
);
    ///// Load behavior /////
    // Q can only transition when load is HIGH.
    load_behavior: assert property (
        @(posedge clk) disable iff (!clk) $rose(load) |-> Q == input_data
    );

    ///// Up/Down behavior /////
    // Q increments when up_down is HIGH and load is LOW.
    up_behavior: assert property (
        @(posedge clk) disable iff (!clk) (up_down == 1'b1) && (load == 1'b0) |-> Q == Q + 1
    );

    // Q decrements when up_down is LOW and load is LOW.
    down_behavior: assert property (
        @(posedge clk) disable iff (!clk) (up_down == 1'b0) && (load == 1'b0) |-> Q == Q - 1
    );

    ///// Sequential logic /////
    // Q should not change when load is LOW and up_down is LOW.
    no_change_behavior: assert property (
        @(posedge clk) disable iff (!clk) (load == 1'b0) && (up_down == 1'b0) |-> Q == Q
    );

endmodule
```