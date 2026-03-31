```systemverilog
module top_module_sva (
    input wire [7:0] num1,
    input wire [7:0] num2,
    output wire [15:0] product
);

    // Combinational logic: product is calculated based on num1 and num2
    // No clock or reset signals present
    // No sequential logic or states to consider

    // Check that the product is correctly calculated
    correct_product: assert property (
        @(posedge clk) disable iff (!RESETn) (product == num1 * num2)
    ) else $error("Product is not correctly calculated");

endmodule
```