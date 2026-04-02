module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [7:0] a,
    input logic [7:0] b,
    output logic [7:0] sum_output,
    output logic [7:0] product_output,
    output logic [7:0] difference_output
);

    // Adder module properties
    // Sum should be correct after reset is deasserted
    adder_sum_correct: assert property (
        @(posedge clk) disable iff (!reset) sum_output == a + b
    );

    // Multiplier module properties
    // Product should be correct after reset is deasserted
    multiplier_product_correct: assert property (
        @(posedge clk) disable iff (!reset) product_output == a * b
    );

    // Difference module properties
    // Difference should be correct after reset is deasserted
    difference_correct: assert property (
        @(posedge clk) disable iff (!reset) difference_output == sum_output - product_output
    );

    // Reset properties
    // Sum should be zero during reset
    reset_sum_zero: assert property (
        @(posedge clk) disable iff (reset) sum_output == 0
    );

    // Product should be zero during reset
    reset_product_zero: assert property (
        @(posedge clk) disable iff (reset) product_output == 0
    );

    // Difference should be zero during reset
    reset_difference_zero: assert property (
        @(posedge clk) disable iff (reset) difference_output == 0
    );

endmodule