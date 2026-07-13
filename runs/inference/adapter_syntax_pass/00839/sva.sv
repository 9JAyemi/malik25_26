module binary_to_gray_sva (
    input logic [8:0] binary,
    input logic [3:0] gray
);

    // gray[3] is a direct copy of binary[8].
    check_gray_bit3_passthrough: assert property (
        @($global_clock) gray[3] == binary[8]
    );

    // gray[2] is binary[8] XOR binary[7].
    check_gray_bit2_xor: assert property (
        @($global_clock) gray[2] == (binary[8] ^ binary[7])
    );

    // gray[1] is binary[7] XOR binary[6].
    check_gray_bit1_xor: assert property (
        @($global_clock) gray[1] == (binary[7] ^ binary[6])
    );

    // gray[0] is binary[6] XOR binary[5].
    check_gray_bit0_xor: assert property (
        @($global_clock) gray[0] == (binary[6] ^ binary[5])
    );

endmodule