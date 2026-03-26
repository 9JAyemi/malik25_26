module binary_to_gray_assertions (
    input logic [2:0] B,
    input logic [2:0] G
);

    // Full output must implement the 3-bit binary-to-Gray conversion.
    check_gray_vector: assert property (
        @($global_clock) G == {B[2], (B[1] ^ B[2]), (B[0] ^ B[1])}
    );

    // Gray MSB must match the binary MSB.
    check_gray_msb_passthrough: assert property (
        @($global_clock) G[2] == B[2]
    );

    // Gray middle bit must be B[1] XOR B[2].
    check_gray_middle_xor: assert property (
        @($global_clock) G[1] == (B[1] ^ B[2])
    );

    // Gray LSB must be B[0] XOR B[1].
    check_gray_lsb_xor: assert property (
        @($global_clock) G[0] == (B[0] ^ B[1])
    );

endmodule