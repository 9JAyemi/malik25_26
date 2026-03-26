module XOR_8_sva (
    input logic        clk,
    input logic [7:0]  A,
    input logic [7:0]  B,
    input logic [7:0]  Z
);

    // Z matches the bitwise XOR of A and B.
    check_z_matches_xor: assert property (
        @(posedge clk) Z === (A ^ B)
    );

    // Bit 0 of Z is A[0] XOR B[0].
    check_z_bit0_xor: assert property (
        @(posedge clk) Z[0] === (A[0] ^ B[0])
    );

    // Bit 1 of Z is A[1] XOR B[1].
    check_z_bit1_xor: assert property (
        @(posedge clk) Z[1] === (A[1] ^ B[1])
    );

    // Bit 2 of Z is A[2] XOR B[2].
    check_z_bit2_xor: assert property (
        @(posedge clk) Z[2] === (A[2] ^ B[2])
    );

    // Bit 3 of Z is A[3] XOR B[3].
    check_z_bit3_xor: assert property (
        @(posedge clk) Z[3] === (A[3] ^ B[3])
    );

    // Bit 4 of Z is A[4] XOR B[4].
    check_z_bit4_xor: assert property (
        @(posedge clk) Z[4] === (A[4] ^ B[4])
    );

    // Bit 5 of Z is A[5] XOR B[5].
    check_z_bit5_xor: assert property (
        @(posedge clk) Z[5] === (A[5] ^ B[5])
    );

    // Bit 6 of Z is A[6] XOR B[6].
    check_z_bit6_xor: assert property (
        @(posedge clk) Z[6] === (A[6] ^ B[6])
    );

    // Bit 7 of Z is A[7] XOR B[7].
    check_z_bit7_xor: assert property (
        @(posedge clk) Z[7] === (A[7] ^ B[7])
    );

    // Equal inputs produce zero.
    check_equal_inputs_zero: assert property (
        @(posedge clk) (A == B) |-> (Z == 8'h00)
    );

    // Zero on B passes A through.
    check_b_zero_passthrough_a: assert property (
        @(posedge clk) (B == 8'h00) |-> (Z === A)
    );

    // Zero on A passes B through.
    check_a_zero_passthrough_b: assert property (
        @(posedge clk) (A == 8'h00) |-> (Z === B)
    );

    // Complementary inputs produce all ones.
    check_complement_inputs_all_ones: assert property (
        @(posedge clk) (A == ~B) |-> (Z == 8'hFF)
    );

    // Stable inputs keep Z stable across samples.
    check_stable_inputs_stable_output: assert property (
        @(posedge clk) ($stable(A) && $stable(B)) |-> $stable(Z)
    );

endmodule