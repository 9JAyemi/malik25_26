module top_module_sva (
    input logic        clk,
    input logic [3:0]  A,
    input logic [3:0]  B,
    input logic [2:0]  OP,
    input logic [3:0]  a,
    input logic [3:0]  b,
    input logic [1:0]  final_output
);

    // final_output must match the compare-driven mapping implemented at top level.
    check_final_output_mapping: assert property (
        @(posedge clk)
        final_output == ((a > b) ? 2'b01 :
                         (a < b) ? 2'b00 :
                                   2'b11)
    );

    // If a is greater than b, final_output must be 01.
    check_gt_maps_to_01: assert property (
        @(posedge clk)
        (a > b) |-> (final_output == 2'b01)
    );

    // If a is less than b, final_output must be 00.
    check_lt_maps_to_00: assert property (
        @(posedge clk)
        (a < b) |-> (final_output == 2'b00)
    );

    // If a equals b, final_output must be 11.
    check_eq_maps_to_11: assert property (
        @(posedge clk)
        (a == b) |-> (final_output == 2'b11)
    );

    // The 10 output is unreachable because comparison_result is never 3'b011.
    check_final_output_never_10: assert property (
        @(posedge clk)
        final_output != 2'b10
    );

endmodule