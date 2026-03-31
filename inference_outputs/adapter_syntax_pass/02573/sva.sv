module ripple_carry_adder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] OUT
);

    // OUT must equal the 4-bit sum of A and B.
    check_out_matches_sum: assert property (
        @(posedge clk) OUT == (A + B)
    );

    // Bit 0 must match the full-adder sum of A[0], B[0], and 0.
    check_lsb_sum: assert property (
        @(posedge clk) OUT[0] == (A[0] ^ B[0])
    );

    // Bit 1 must match the full-adder sum of A[1], B[1], and carry from bit 0.
    check_bit1_sum: assert property (
        @(posedge clk) OUT[1] == (A[1] ^ B[1] ^ (A[0] & B[0]))
    );

    // Bit 2 must match the full-adder sum of A[2], B[2], and carry from bit 1.
    check_bit2_sum: assert property (
        @(posedge clk) OUT[2] == (A[2] ^ B[2] ^
                                  ((A[1] & B[1]) |
                                   ((A[1] ^ B[1]) & (A[0] & B[0]))))
    );

    // Bit 3 must match the full-adder sum of A[3], B[3], and carry from bit 2.
    check_bit3_sum: assert property (
        @(posedge clk) OUT[3] == (A[3] ^ B[3] ^
                                  ((A[2] & B[2]) |
                                   ((A[2] ^ B[2]) &
                                    ((A[1] & B[1]) |
                                     ((A[1] ^ B[1]) & (A[0] & B[0])))))))
    );

endmodule