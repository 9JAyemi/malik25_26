module nand_decoder_sva (
    input logic [1:0] in,
    input logic [3:0] out
);

    // Output bits are all the same.
    check_out_bits_equal: assert property (
        @($global_clock) out[0] == out[1] && out[1] == out[2] && out[2] == out[3]
    );

    // Output matches the inverted AND of the inputs.
    check_out_matches_inverted_and: assert property (
        @($global_clock) out[0] == ~(in[0] & in[1])
    );

    // When both inputs are high, the output is low.
    check_both_inputs_high_drive_low: assert property (
        @($global_clock) (in[0] && in[1]) |-> (out[0] == 1'b0)
    );

    // When both inputs are low, the output is high.
    check_both_inputs_low_drive_high: assert property (
        @($global_clock) (!in[0] && !in[1]) |-> (out[0] == 1'b1)
    );

    // When the inputs differ, the output is high.
    check_inputs_differ_drive_high: assert property (
        @($global_clock) (in[0] ^ in[1]) |-> (out[0] == 1'b1)
    );

endmodule