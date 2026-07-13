module top_module_sva (
    input logic        clk,
    input logic [3:0]  A,
    input logic [3:0]  B,
    input logic [7:0]  C,
    input logic [7:0]  final_output,
    input logic [7:0]  multiplier_output,
    input logic [1:0]  comparator_output
);

    // multiplier_output is the unsigned product of A and B.
    check_multiplier_product: assert property (
        @(posedge clk) multiplier_output == (A * B)
    );

    // comparator_output is 00 when the product equals C.
    check_comparator_equal_code: assert property (
        @(posedge clk) (multiplier_output == C) |-> (comparator_output == 2'b00)
    );

    // comparator_output is 01 when the product is greater than C.
    check_comparator_greater_code: assert property (
        @(posedge clk) (multiplier_output > C) |-> (comparator_output == 2'b01)
    );

    // comparator_output is 10 when the product is less than C.
    check_comparator_less_code: assert property (
        @(posedge clk) (multiplier_output < C) |-> (comparator_output == 2'b10)
    );

    // comparator_output never uses the unused 11 encoding.
    check_comparator_valid_code: assert property (
        @(posedge clk) comparator_output != 2'b11
    );

    // final_output adds the comparator code to the multiplier output.
    check_final_output_sum: assert property (
        @(posedge clk) final_output == (multiplier_output + {2'b0, comparator_output})
    );

    // final_output matches the product when the product equals C.
    check_final_output_equal_case: assert property (
        @(posedge clk) ((A * B) == C) |-> (final_output == (A * B))
    );

    // final_output is product plus 1 when the product is greater than C.
    check_final_output_greater_case: assert property (
        @(posedge clk) ((A * B) > C) |-> (final_output == ((A * B) + 8'd1))
    );

    // final_output is product plus 2 when the product is less than C.
    check_final_output_less_case: assert property (
        @(posedge clk) ((A * B) < C) |-> (final_output == ((A * B) + 8'd2))
    );

    // final_output matches the complete top-level combinational function.
    check_top_level_function: assert property (
        @(posedge clk)
        final_output == ((A * B) + (((A * B) == C) ? 8'd0 : (((A * B) > C) ? 8'd1 : 8'd2)))
    );

endmodule