module top_module_assertions (
    input logic        clk,
    input logic [15:0] in,
    input logic        out,
    input logic [7:0]  out1,
    input logic [7:0]  out2
);

    // out1 must always mirror the low byte of in.
    check_splitter_lower_byte: assert property (
        @(posedge clk) out1 == in[7:0]
    );

    // out2 must always mirror the high byte of in.
    check_splitter_upper_byte: assert property (
        @(posedge clk) out2 == in[15:8]
    );

    // out must be the AND of bit 0 from each split byte.
    check_and_from_split_bits: assert property (
        @(posedge clk) out == (out2[0] & out1[0])
    );

    // out must match the direct function of in[8] and in[0].
    check_direct_output_function: assert property (
        @(posedge clk) out == (in[8] & in[0])
    );

    // A high out requires both selected input bits to be high.
    check_output_high_requires_both_bits: assert property (
        @(posedge clk) out |-> (in[8] && in[0])
    );

    // A low in[0] forces out low.
    check_lower_bit_zero_forces_low: assert property (
        @(posedge clk) !in[0] |-> !out
    );

    // A low in[8] forces out low.
    check_upper_bit_zero_forces_low: assert property (
        @(posedge clk) !in[8] |-> !out
    );

    // Both selected input bits high force out high.
    check_both_bits_high_force_high: assert property (
        @(posedge clk) (in[8] && in[0]) |-> out
    );

endmodule