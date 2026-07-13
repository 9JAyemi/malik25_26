module top_module_assertions (
    input logic clk,
    input logic [2:0] a,
    input logic [2:0] b,
    input logic [2:0] out_or_bitwise,
    input logic out_or_logical,
    input logic [5:0] out_not
);

    // Bitwise OR output matches the OR of a and b.
    check_out_or_bitwise_matches_inputs: assert property (
        @(posedge clk) out_or_bitwise == (a | b)
    );

    // Lower half of out_not is the inversion of a.
    check_out_not_lower_matches_a_inversion: assert property (
        @(posedge clk) out_not[2:0] == ~a
    );

    // Upper half of out_not is the inversion of b.
    check_out_not_upper_matches_b_inversion: assert property (
        @(posedge clk) out_not[5:3] == ~b
    );

    // Full out_not bus matches the concatenated inversions of b and a.
    check_out_not_concatenation: assert property (
        @(posedge clk) out_not == {~b, ~a}
    );

    // out_or_logical is high only when the bitwise OR equals 3'b111.
    check_out_or_logical_matches_inputs: assert property (
        @(posedge clk) out_or_logical == ((a | b) == 3'b111)
    );

    // out_or_logical matches the reduction-AND of out_or_bitwise.
    check_out_or_logical_matches_out_or_bitwise: assert property (
        @(posedge clk) out_or_logical == (&out_or_bitwise)
    );

endmodule