module top_module_sva (
    input logic        clk,
    input logic [15:0] in,
    input logic        out
);

    // Output matches the AND of the two split input bits.
    check_output_matches_split_and: assert property (
        @(posedge clk) out == (in[15] & in[0])
    );

    // A low MSB forces the output low.
    check_msb_low_forces_output_low: assert property (
        @(posedge clk) !in[15] |-> !out
    );

    // A low LSB forces the output low.
    check_lsb_low_forces_output_low: assert property (
        @(posedge clk) !in[0] |-> !out
    );

    // A high output requires both split bits to be high.
    check_output_high_requires_both_bits_high: assert property (
        @(posedge clk) out |-> (in[15] && in[0])
    );

    // Both split bits high drive the output high.
    check_both_bits_high_drive_output_high: assert property (
        @(posedge clk) (in[15] && in[0]) |-> out
    );

endmodule