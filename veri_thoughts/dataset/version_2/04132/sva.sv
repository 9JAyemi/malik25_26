module gray_code_converter_sva (
    input logic [3:0] bin,
    input logic [3:0] gray
);

    // gray[3] is a direct copy of bin[3].
    check_gray_msb_passthrough: assert property (
        @($global_clock) gray[3] == bin[3]
    );

    // gray[2] is the XOR of bin[3] and bin[2].
    check_gray_bit2_xor: assert property (
        @($global_clock) gray[2] == (bin[3] ^ bin[2])
    );

    // gray[1] is the XOR of bin[2] and bin[1].
    check_gray_bit1_xor: assert property (
        @($global_clock) gray[1] == (bin[2] ^ bin[1])
    );

    // gray[0] is the XOR of bin[1] and bin[0].
    check_gray_lsb_xor: assert property (
        @($global_clock) gray[0] == (bin[1] ^ bin[0])
    );

endmodule