module binary_counter_sva (
    input logic clk,
    input logic [3:0] reset,
    input logic [3:0] enable,
    input logic [3:0] count
);
    ///// Reset behavior /////
    // At reset, count must be driven to 0.
    reset: assert property (
        @(posedge clk) disable iff (reset == 4'b0) count == 4'b0
    );

    ///// Enable behavior /////
    // When enable is high, count should increment on each clock edge.
    enable: assert property (
        @(posedge clk) disable iff (reset == 4'b0) (enable == 4'b1) |-> count == count + 1
    );

    // When enable is low, count should not change.
    disable: assert property (
        @(posedge clk) disable iff (reset == 4'b0) (enable == 4'b0) |-> count == count
    );
endmodule