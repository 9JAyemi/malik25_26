module bin2gray_sva (
    input logic [3:0] bin,
    input logic [3:0] gray
);

    // gray[3] is a direct copy of bin[3].
    check_gray_bit3_passthrough: assert property (
        @($global_clock) gray[3] == bin[3]
    );

    // gray[2] is bin[3] XOR bin[2].
    check_gray_bit2_xor: assert property (
        @($global_clock) gray[2] == (bin[3] ^ bin[2])
    );

    // gray[1] is bin[2] XOR bin[1].
    check_gray_bit1_xor: assert property (
        @($global_clock) gray[1] == (bin[2] ^ bin[1])
    );

    // gray[0] is bin[1] XOR bin[0].
    check_gray_bit0_xor: assert property (
        @($global_clock) gray[0] == (bin[1] ^ bin[0])
    );

    // The full gray vector matches the implemented binary-to-Gray conversion.
    check_gray_vector_mapping: assert property (
        @($global_clock) gray == {bin[3], (bin[3] ^ bin[2]), (bin[2] ^ bin[1]), (bin[1] ^ bin[0])}
    );

endmodule