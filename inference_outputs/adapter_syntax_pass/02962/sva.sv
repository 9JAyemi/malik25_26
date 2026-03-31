module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] sum_output,
    input logic [7:0] product_output,
    input logic [7:0] difference_output
);

    // Reset clears the adder output on the next clock.
    check_sum_clears_on_reset: assert property (
        @(posedge clk) reset |=> (sum_output == 8'h00)
    );

    // Reset clears the multiplier output on the next clock.
    check_product_clears_on_reset: assert property (
        @(posedge clk) reset |=> (product_output == 8'h00)
    );

    // Reset clears the difference output on the next clock.
    check_difference_clears_on_reset: assert property (
        @(posedge clk) reset |=> (difference_output == 8'h00)
    );

    // The adder output is the previous cycle's a+b.
    check_sum_matches_previous_inputs: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (sum_output == ($past(a) + $past(b)))
    );

    // The multiplier output is the previous cycle's a*b.
    check_product_matches_previous_inputs: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (product_output == ($past(a) * $past(b)))
    );

    // The difference output is the previous cycle's sum_output - product_output.
    check_difference_matches_previous_outputs: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (difference_output == ($past(sum_output) - $past(product_output)))
    );

    // The difference output is the previous cycle's a + b - (a * b).
    check_difference_matches_previous_inputs: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (difference_output == ($past(a) + $past(b) - ($past(a) * $past(b))))
    );

endmodule