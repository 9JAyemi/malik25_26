```systemverilog
module multiplier_sva (
    input logic clk,
    input logic reset,
    input logic sel,
    input signed [7:0] a,
    input signed [7:0] b,
    output signed [15:0] out
);

    // Reset behavior: At reset, both product and sum should be 0
    reset_behavior: assert property (
        @(posedge clk) disable iff (!reset) (reset |-> (product == 16'b0) && (sum == 16'b0))
    );

    // Sequential logic for product calculation
    product_calculation: assert property (
        @(posedge clk) disable iff (!reset) (sel |-> (product == a * b))
    );

    // Sequential logic for sum calculation
    sum_calculation: assert property (
        @(posedge clk) disable iff (!reset) (!sel |-> (sum == a + b))
    );

    // Output selection logic
    output_selection: assert property (
        @(posedge clk) disable iff (!reset) (out == (sel ? sum : product))
    );

endmodule
```