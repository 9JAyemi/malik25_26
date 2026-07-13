module add4bit_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] Y
);
    // Output equals lower 4 bits of A+B (mod-16 sum).
    check_sum_mod16: assert property (
        @(posedge clk) disable iff (1'b0) Y == (A + B)[3:0]
    );

    // When no overflow, Y equals the full sum.
    check_no_overflow_gives_exact_sum: assert property (
        @(posedge clk) disable iff (1'b0) ((A + B) <= 5'd15) |-> (Y == (A + B))
    );

    // When overflow occurs, Y equals sum minus 16.
    check_overflow_wraps_sub16: assert property (
        @(posedge clk) disable iff (1'b0) ((A + B) > 5'd15) |-> (Y == ((A + B) - 5'd16))
    );

    // On overflow, result is less than both operands.
    check_overflow_result_less_than_operands: assert property (
        @(posedge clk) disable iff (1'b0) ((A + B) > 5'd15) |-> (Y < A && Y < B)
    );

    // Adding zero on B passes A through.
    check_zero_b_passthrough: assert property (
        @(posedge clk) disable iff (1'b0) (B == 4'd0) |-> (Y == A)
    );

    // Adding zero on A passes B through.
    check_zero_a_passthrough: assert property (
        @(posedge clk) disable iff (1'b0) (A == 4'd0) |-> (Y == B)
    );

    // LSB of sum is XOR of operand LSBs.
    check_bit0_sum: assert property (
        @(posedge clk) disable iff (1'b0) Y[0] == (A[0] ^ B[0])
    );

    // Bit1 of sum equals A1 ^ B1 ^ carry0 (carry0 = A0 & B0).
    check_bit1_sum_with_carry0: assert property (
        @(posedge clk) disable iff (1'b0) Y[1] == (A[1] ^ B[1]) ^ (A[0] & B[0])
    );

    // Bit2 of sum equals A2 ^ B2 ^ carry1 (carry1 = (A1&B1) | ((A1^B1)&carry0)).
    check_bit2_sum_with_carry1: assert property (
        @(posedge clk) disable iff (1'b0)
            Y[2] == (A[2] ^ B[2]) ^ ( (A[1] & B[1]) | ((A[1] ^ B[1]) & (A[0] & B[0])) )
    );

    // Bit3 of sum equals A3 ^ B3 ^ carry2 (carry2 = (A2&B2) | ((A2^B2)&carry1)).
    check_bit3_sum_with_carry2: assert property (
        @(posedge clk) disable iff (1'b0)
            Y[3] == (A[3] ^ B[3]) ^ (
                        (A[2] & B[2]) |
                        ((A[2] ^ B[2]) &
                            ( (A[1] & B[1]) | ((A[1] ^ B[1]) & (A[0] & B[0])) )
                        )
                    )
    );
endmodule