module bin2gray_sva (
    input logic [3:0] B,
    input logic [3:0] G
);

    // No RTL clock or reset; sample combinational behavior on the formal global clock.

    // G[3] must copy the MSB of B.
    check_g3_msb_copy: assert property (
        @($global_clock) G[3] == B[3]
    );

    // G[2] must be B[3] XOR B[2].
    check_g2_xor_mapping: assert property (
        @($global_clock) G[2] == (B[3] ^ B[2])
    );

    // G[1] must be B[2] XOR B[1].
    check_g1_xor_mapping: assert property (
        @($global_clock) G[1] == (B[2] ^ B[1])
    );

    // G[0] must be B[1] XOR B[0].
    check_g0_xor_mapping: assert property (
        @($global_clock) G[0] == (B[1] ^ B[0])
    );

    // The full Gray code output must match the binary input encoding.
    check_full_gray_encoding: assert property (
        @($global_clock) G == {B[3], (B[3] ^ B[2]), (B[2] ^ B[1]), (B[1] ^ B[0])}
    );

endmodule