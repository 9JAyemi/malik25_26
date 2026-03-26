module Adder4_sva (
    input logic       clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [4:0] S
);

    // S[0] is the XOR of A[0] and B[0].
    check_sum_bit0_xor: assert property (
        @(posedge clk) S[0] == (A[0] ^ B[0])
    );

    // S[1] is the XOR of A[1] and B[1].
    check_sum_bit1_xor: assert property (
        @(posedge clk) S[1] == (A[1] ^ B[1])
    );

    // S[2] is the XOR of A[2] and B[2].
    check_sum_bit2_xor: assert property (
        @(posedge clk) S[2] == (A[2] ^ B[2])
    );

    // S[3] is the XOR of A[3] and B[3].
    check_sum_bit3_xor: assert property (
        @(posedge clk) S[3] == (A[3] ^ B[3])
    );

    // S[4] is the reduction XNOR of the bitwise XOR result.
    check_msb_parity_xnor: assert property (
        @(posedge clk) S[4] == (~^(A ^ B))
    );

endmodule