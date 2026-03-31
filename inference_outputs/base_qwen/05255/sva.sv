```systemverilog
module binary_multiplier_sva (
    input logic clk,
    input logic reset,
    input logic [15:0] a,
    input logic [15:0] b,
    input logic [31:0] result
);
    ///// Device reset /////
    // At reset assertion, the result must be driven to 0.
    reset: assert property (
        @(posedge clk) disable iff (!reset) result == 32'b0
    );

    ///// Multiplication logic /////
    // The result should be the product of a and b after each clock cycle.
    multiplication: assert property (
        @(posedge clk) disable iff (!reset) result == a * b
    );
endmodule
```