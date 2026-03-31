module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] sum_output,
    input logic [7:0] product_output,
    input logic [7:0] difference_output
);

// sum_output is the 8-bit sum of a and b on the next clock.
    check_sum_next_cycle: assert property (
        @(posedge clk) disable iff (reset) 1'b1 |=> (sum_output == ($past(a) + $past(b)))
    );

// product_output is the 8-bit product of a and b on the next clock.
    check_product_next_cycle: assert property (
        @(posedge clk) disable iff (reset) 1'b1 |=> (product_output == ($past(a) * $past(b)))
    );

// difference_output is the 8-bit difference of sum_output and product_output on the next clock.
    check_difference_next_cycle: assert property (
        @(posedge clk) disable iff (reset) 1'b1 |=> (difference_output == ($past(sum_output) - $past(product_output)))
    );

// Reset clears sum_output to zero on the next clock.
    check_sum_reset_clears: assert property (
        @(posedge clk) reset |=> (sum_output == 8'h00)
    );

// Reset clears product_output to zero on the next clock.
    check_product_reset_clears: assert property (
        @(posedge clk) reset |=> (product_output == 8'h00)
    );

// Reset clears difference_output to zero on the next clock.
    check_difference_reset_clears: assert property (
        @(posedge clk) reset |=> (difference_output == 8'h00)
    );

endmodule
