module four_bit_adder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] sum
);

    // Sum must equal the 4-bit addition result.
    check_sum_matches_addition: assert property (
        @(posedge clk) sum == ((A + B) & 4'hF)
    );

    // Adding zero on B leaves A unchanged.
    check_b_zero_identity: assert property (
        @(posedge clk) (B == 4'h0) |-> (sum == A)
    );

    // Adding zero on A leaves B unchanged.
    check_a_zero_identity: assert property (
        @(posedge clk) (A == 4'h0) |-> (sum == B)
    );

    // Bit 0 is the XOR of the least significant input bits.
    check_bit0_xor: assert property (
        @(posedge clk) sum[0] == (A[0] ^ B[0])
    );

    // Bit 1 includes the carry from bit 0.
    check_bit1_ripple: assert property (
        @(posedge clk) sum[1] == (A[1] ^ B[1] ^ (A[0] & B[0]))
    );

    // Bit 2 includes the carry from the lower two bits.
    check_bit2_ripple: assert property (
        @(posedge clk)
        sum[2] == (A[2] ^ B[2] ^
                   ((A[1] & B[1]) |
                    (A[1] & (A[0] & B[0])) |
                    (B[1] & (A[0] & B[0]))))
    );

    // Bit 3 includes the carry from the lower three bits.
    check_bit3_ripple: assert property (
        @(posedge clk)
        sum[3] == (A[3] ^ B[3] ^
                   ((A[2] & B[2]) |
                    (A[2] & ((A[1] & B[1]) |
                             (A[1] & (A[0] & B[0])) |
                             (B[1] & (A[0] & B[0])))) |
                    (B[2] & ((A[1] & B[1]) |
                             (A[1] & (A[0] & B[0])) |
                             (B[1] & (A[0] & B[0]))))))
    );

    // Stable inputs must keep the sampled sum stable.
    check_stable_inputs_keep_stable_sum: assert property (
        @(posedge clk) (!$initstate && $stable(A) && $stable(B)) |-> $stable(sum)
    );

    // 0xF + 0x1 must roll over in 4-bit arithmetic.
    check_rollover_f_plus_1: assert property (
        @(posedge clk) (A == 4'hF && B == 4'h1) |-> (sum == 4'h0)
    );

    // Complementary operands must produce 0xF.
    check_complementary_inputs: assert property (
        @(posedge clk) (B == ~A) |-> (sum == 4'hF)
    );

endmodule