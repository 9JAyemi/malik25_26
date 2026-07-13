module four_bit_adder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] S,
    input logic COUT
);

    // S[0] is the XOR of A[0], B[0], and the unused carry-in.
    check_sum_bit0: assert property (
        @(posedge clk) S[0] == (A[0] ^ B[0])
    );

    // S[1] is the XOR of A[1], B[1], and the carry from bit 0.
    check_sum_bit1: assert property (
        @(posedge clk) S[1] == (A[1] ^ B[1] ^ (A[0] & B[0]))
    );

    // S[2] is the XOR of A[2], B[2], and the carry from bit 1.
    check_sum_bit2: assert property (
        @(posedge clk) S[2] == (A[2] ^ B[2] ^
            ((A[1] & B[1]) | ((A[1] ^ B[1]) & (A[0] & B[0]))))
    );

    // S[3] is the XOR of A[3], B[3], and the carry from bit 2.
    check_sum_bit3: assert property (
        @(posedge clk) S[3] == (A[3] ^ B[3] ^
            ((A[2] & B[2]) | ((A[2] ^ B[2]) &
                ((A[1] & B[1]) | ((A[1] ^ B[1]) & (A[0] & B[0)))))))
    );

    // COUT is the carry out from the final full adder stage.
    check_cout: assert property (
        @(posedge clk) COUT == ((A[3] & B[3]) | ((A[3] ^ B[3]) &
            ((A[2] & B[2]) | ((A[2] ^ B[2]) &
                ((A[1] & B[1]) | ((A[1] ^ B[1]) & (A[0] & B[0]))))))))
    );

    // The 5-bit output matches the arithmetic sum of A and B.
    check_total_sum: assert property (
        @(posedge clk) {COUT, S} == ({1'b0, A} + {1'b0, B})
    );

endmodule