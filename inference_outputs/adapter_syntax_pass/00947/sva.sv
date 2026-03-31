module top_module_sva (
    input logic clk,
    input logic [99:0] in,
    input logic out_and,
    input logic out_or,
    input logic out_xor
);

    // out_and must equal the reduction AND of in.
    check_out_and_matches_reduction_and: assert property (
        @(posedge clk) out_and == (&in)
    );

    // out_or must equal the reduction OR of in.
    check_out_or_matches_reduction_or: assert property (
        @(posedge clk) out_or == (|in)
    );

    // out_xor must equal the reduction XOR of in.
    check_out_xor_matches_reduction_xor: assert property (
        @(posedge clk) out_xor == (^in)
    );

    // out_and and out_or must never be high together.
    check_out_and_or_mutex: assert property (
        @(posedge clk) !(out_and && out_or)
    );

    // out_and must be high when all input bits are high.
    check_out_and_high_when_all_high: assert property (
        @(posedge clk) (&in) |-> out_and
    );

    // out_and must be low when any input bit is low.
    check_out_and_low_when_any_low: assert property (
        @(posedge clk) (|in) |-> !out_and
    );

    // out_or must be high when any input bit is high.
    check_out_or_high_when_any_high: assert property (
        @(posedge clk) (|in) |-> out_or
    );

    // out_or must be low when all input bits are low.
    check_out_or_low_when_all_low: assert property (
        @(posedge clk) (&in) |-> !out_or
    );

    // out_xor must be low when the number of high input bits is even.
    check_out_xor_low_when_even_ones: assert property (
        @(posedge clk) ((^in) == 1'b0) |-> !out_xor
    );

    // out_xor must be high when the number of high input bits is odd.
    check_out_xor_high_when_odd_ones: assert property (
        @(posedge clk) ((^in) == 1'b1) |-> out_xor
    );

endmodule