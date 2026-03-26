module top_module_sva (
    input logic clk,
    input logic [2:0] a,
    input logic [2:0] b,
    input logic [2:0] out_or_bitwise,
    input logic out_or_logical,
    input logic [5:0] out_not
);

    // Checks the bitwise OR output.
    check_out_or_bitwise_value: assert property (
        @(posedge clk) out_or_bitwise == (a | b)
    );

    // Checks the logical OR output.
    check_out_or_logical_value: assert property (
        @(posedge clk) out_or_logical == ((a != 3'b000) || (b != 3'b000))
    );

    // Checks logical OR matches whether the bitwise OR is non-zero.
    check_out_or_logical_matches_bitwise_or: assert property (
        @(posedge clk) out_or_logical == (out_or_bitwise != 3'b000)
    );

    // Checks the upper half of out_not is the inverse of b.
    check_out_not_upper_inverts_b: assert property (
        @(posedge clk) out_not[5:3] == ~b
    );

    // Checks the lower half of out_not is the inverse of a.
    check_out_not_lower_inverts_a: assert property (
        @(posedge clk) out_not[2:0] == ~a
    );

    // Checks the full out_not bus matches the concatenated inversions.
    check_out_not_concat_value: assert property (
        @(posedge clk) out_not == {~b, ~a}
    );

endmodule