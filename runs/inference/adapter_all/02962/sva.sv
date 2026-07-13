module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] sum_output,
    input logic [7:0] product_output,
    input logic [7:0] difference_output
);

    // Reset clears all registered outputs on the next clock.
    check_reset_clears_outputs: assert property (
        @(posedge clk) reset |=> (sum_output == 8'h00) && (product_output == 8'h00) && (difference_output == 8'h00)
    );

    // sum_output is the registered sum of a and b from the previous cycle.
    check_sum_register_update: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (sum_output == $past(a + b))
    );

    // product_output is the registered product of a and b from the previous cycle.
    check_product_register_update: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (product_output == $past(a * b))
    );

    // difference_output is the registered difference of a and b from the previous cycle.
    check_difference_register_update: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (difference_output == $past(a - b))
    );

    // difference_output matches the difference of sum_output and product_output from the previous cycle.
    check_difference_matches_registered_ops: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (difference_output == $past(sum_output - product_output))
    );

    // After reset, the next cycle still sees all outputs cleared.
    check_reset_release_clears_outputs: assert property (
        @(posedge clk) reset ##1 !reset |-> (sum_output == 8'h00) && (product_output == 8'h00) && (difference_output == 8'h00)
    );

endmodule