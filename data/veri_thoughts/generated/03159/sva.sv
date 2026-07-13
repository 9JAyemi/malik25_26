module ones_complement_assertions (
    input logic [3:0] in,
    input logic [3:0] out
);

    // Output bus is always the bitwise inverse of the input bus.
    check_out_matches_ones_complement: assert property (
        @($global_clock) out == ~in
    );

    // Output bit 0 is the inverse of input bit 0.
    check_out_bit0_inverse: assert property (
        @($global_clock) out[0] == ~in[0]
    );

    // Output bit 1 is the inverse of input bit 1.
    check_out_bit1_inverse: assert property (
        @($global_clock) out[1] == ~in[1]
    );

    // Output bit 2 is the inverse of input bit 2.
    check_out_bit2_inverse: assert property (
        @($global_clock) out[2] == ~in[2]
    );

    // Output bit 3 is the inverse of input bit 3.
    check_out_bit3_inverse: assert property (
        @($global_clock) out[3] == ~in[3]
    );

endmodule