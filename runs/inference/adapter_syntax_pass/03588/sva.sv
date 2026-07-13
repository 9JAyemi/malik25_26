module bitwise_and_sva (
    input logic clk,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [7:0] C
);

    // C must equal the bitwise AND of A and B.
    check_output_matches_and: assert property (
        @(posedge clk) C == (A & B)
    );

    // C[0] must equal A[0] AND B[0].
    check_bit0_matches_and: assert property (
        @(posedge clk) C[0] == (A[0] & B[0])
    );

    // C[1] must equal A[1] AND B[1].
    check_bit1_matches_and: assert property (
        @(posedge clk) C[1] == (A[1] & B[1])
    );

    // C[2] must equal A[2] AND B[2].
    check_bit2_matches_and: assert property (
        @(posedge clk) C[2] == (A[2] & B[2])
    );

    // C[3] must equal A[3] AND B[3].
    check_bit3_matches_and: assert property (
        @(posedge clk) C[3] == (A[3] & B[3])
    );

    // C[4] must equal A[4] AND B[4].
    check_bit4_matches_and: assert property (
        @(posedge clk) C[4] == (A[4] & B[4])
    );

    // C[5] must equal A[5] AND B[5].
    check_bit5_matches_and: assert property (
        @(posedge clk) C[5] == (A[5] & B[5])
    );

    // C[6] must equal A[6] AND B[6].
    check_bit6_matches_and: assert property (
        @(posedge clk) C[6] == (A[6] & B[6])
    );

    // C[7] must equal A[7] AND B[7].
    check_bit7_matches_and: assert property (
        @(posedge clk) C[7] == (A[7] & B[7])
    );

endmodule