module bin_to_gray_sva (
    input logic [3:0] bin,
    input logic [3:0] gray
);

    // Combinational RTL with no explicit clock or reset; sample on the formal global clock.
    // Key interface: 4-bit binary input mapped to a 4-bit Gray-code-style output.

    // gray[0] matches bin[0] XOR bin[1].
    check_gray_bit0_xor: assert property (
        @($global_clock) gray[0] === (bin[0] ^ bin[1])
    );

    // gray[1] matches bin[1] XOR bin[2].
    check_gray_bit1_xor: assert property (
        @($global_clock) gray[1] === (bin[1] ^ bin[2])
    );

    // gray[2] matches bin[2] XOR bin[3].
    check_gray_bit2_xor: assert property (
        @($global_clock) gray[2] === (bin[2] ^ bin[3])
    );

    // gray[3] passes through bin[3].
    check_gray_bit3_passthrough: assert property (
        @($global_clock) gray[3] === bin[3]
    );

    // The full gray vector matches the RTL bit mapping.
    check_gray_vector_mapping: assert property (
        @($global_clock) gray === {bin[3], (bin[2] ^ bin[3]), (bin[1] ^ bin[2]), (bin[0] ^ bin[1])}
    );

endmodule