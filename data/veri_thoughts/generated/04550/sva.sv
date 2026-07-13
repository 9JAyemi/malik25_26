module ones_comp_sva (
    input logic [7:0] in,
    input logic [7:0] out
);

    // Output matches the bitwise complement of the input.
    check_output_is_ones_complement: assert property (
        @($global_clock) out == ~in
    );

    // Input and output XOR to all ones.
    check_input_output_xor_all_ones: assert property (
        @($global_clock) (in ^ out) == 8'hFF
    );

    // Output bit 0 complements input bit 0.
    check_bit0_complement: assert property (
        @($global_clock) out[0] == ~in[0]
    );

    // Output bit 1 complements input bit 1.
    check_bit1_complement: assert property (
        @($global_clock) out[1] == ~in[1]
    );

    // Output bit 2 complements input bit 2.
    check_bit2_complement: assert property (
        @($global_clock) out[2] == ~in[2]
    );

    // Output bit 3 complements input bit 3.
    check_bit3_complement: assert property (
        @($global_clock) out[3] == ~in[3]
    );

    // Output bit 4 complements input bit 4.
    check_bit4_complement: assert property (
        @($global_clock) out[4] == ~in[4]
    );

    // Output bit 5 complements input bit 5.
    check_bit5_complement: assert property (
        @($global_clock) out[5] == ~in[5]
    );

    // Output bit 6 complements input bit 6.
    check_bit6_complement: assert property (
        @($global_clock) out[6] == ~in[6]
    );

    // Output bit 7 complements input bit 7.
    check_bit7_complement: assert property (
        @($global_clock) out[7] == ~in[7]
    );

endmodule