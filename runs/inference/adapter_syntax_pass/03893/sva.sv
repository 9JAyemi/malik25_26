module ripple_carry_adder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] SUM
);

    // SUM[0] is the XOR of A[0] and B[0].
    check_sum0_xor: assert property (
        @(posedge clk) SUM[0] == (A[0] ^ B[0])
    );

    // SUM[1] is the XOR of A[1], B[1], and the carry from bit 0.
    check_sum1_with_carry0: assert property (
        @(posedge clk)
        SUM[1] == (A[1] ^ B[1] ^ ((A[0] & B[0]) | ((A[0] ^ B[0]) & 1'b1)))
    );

    // SUM[2] is the XOR of A[2], B[2], and the carry from bit 1.
    check_sum2_with_carry1: assert property (
        @(posedge clk)
        SUM[2] == (A[2] ^ B[2] ^
                   ((A[1] & B[1]) |
                    ((A[1] ^ B[1]) &
                     ((A[0] & B[0]) | ((A[0] ^ B[0]) & 1'b1))))))
    );

    // SUM[3] is the XOR of A[3], B[3], and the carry from bit 2.
    check_sum3_with_carry2: assert property (
        @(posedge clk)
        SUM[3] == (A[3] ^ B[3] ^
                   ((A[2] & B[2]) |
                    ((A[2] ^ B[2]) &
                     ((A[1] & B[1]) |
                      ((A[1] ^ B[1]) &
                       ((A[0] & B[0]) | ((A[0] ^ B[0]) & 1'b1))))))))
    );

    // The 4-bit output is the bitwise XOR of A and B.
    check_sum_vector_xor: assert property (
        @(posedge clk) SUM == (A ^ B)
    );

endmodule