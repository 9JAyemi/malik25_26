```systemverilog
module counter_sva (
    input logic clk,
    input logic reset,
    input logic enable,
    output logic [1:0] count
);
    ///// Counter reset /////
    // At reset, the counter must be driven to 0.
    reset: assert property (
        @(posedge clk) reset |-> (count == 2'b0)
    );

    ///// Counter enable /////
    // When enable is high, the counter should increment.
    increment: assert property (
        @(posedge clk) disable iff (reset) enable |-> count == count + 1
    );

    ///// Counter disable /////
    // When enable is low, the counter should not increment.
    no_increment: assert property (
        @(posedge clk) disable iff (reset) !enable |-> count == count
    );
endmodule
```