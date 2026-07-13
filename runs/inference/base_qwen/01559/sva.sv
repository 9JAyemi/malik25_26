module counter_sva (
    input logic clk,
    input logic rst,
    input logic enable,
    input logic [31:0] count
);
    ///// Counter reset /////
    // At reset, the counter must be driven to 0.
    reset: assert property (
        @(posedge clk) rst |-> (count == 32'b0)
    );

    ///// Counter enable /////
    // When enable is high, the counter should increment.
    enable: assert property (
        @(posedge clk) disable iff (rst) enable |-> count == count + 1
    );

    ///// Counter disable /////
    // When enable is low, the counter should not increment.
    disable: assert property (
        @(posedge clk) disable iff (rst) !enable |-> count == count
    );
endmodule