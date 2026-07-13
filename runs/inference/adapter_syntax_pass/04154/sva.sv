module invert_msb_sva (
    input logic [3:0] i_binary,
    input logic [3:0] o_inverted
);

    // Output must always match the RTL concatenation.
    check_output_matches_rtl: assert property (
        @($global_clock) o_inverted == {~i_binary[3], i_binary[2:0]}
    );

    // The inverted MSB must be the inverse of the input MSB.
    check_msb_inversion: assert property (
        @($global_clock) o_inverted[3] == ~i_binary[3]
    );

    // The lower three output bits must pass through the input bits.
    check_lower_bits_passthrough: assert property (
        @($global_clock) o_inverted[2:0] == i_binary[2:0]
    );

endmodule