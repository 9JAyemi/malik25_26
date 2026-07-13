module ripple_adder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic [3:0] S,
    input logic Cout
);

    // S[0] is the XOR of A[0], B[0], and Cin.
    check_sum_bit0_xor: assert property (
        @(posedge clk) S[0] == (A[0] ^ B[0] ^ Cin)
    );

    // S[1] is the XOR of A[1], B[1], and the carry from bit 0.
    check_sum_bit1_xor_with_carry0: assert property (
        @(posedge clk) S[1] == (A[1] ^ B[1] ^ ((A[0] & B[0]) | ((A[0] ^ B[0]) & Cin)))
    );

    // S[2] is the XOR of A[2], B[2], and the carry from bit 1.
    check_sum_bit2_xor_with_carry1: assert property (
        @(posedge clk) S[2] == (A[2] ^ B[2] ^ (
            (A[1] & B[1]) |
            ((A[1] ^ B[1]) & ((A[0] & B[0]) | ((A[0] ^ B[0]) & Cin)))
        ))
    );

    // S[3] is the XOR of A[3], B[3], and the carry from bit 2.
    check_sum_bit3_xor_with_carry2: assert property (
        @(posedge clk) S[3] == (A[3] ^ B[3] ^ (
            (A[2] & B[2]) |
            ((A[2] ^ B[2]) & (
                (A[1] & B[1]) |
                ((A[1] ^ B[1]) & ((A[0] & B[0]) | ((A[0] ^ B[0]) & Cin)))
            ))
        ))
    );

    // Cout is the carry out from the final full adder.
    check_cout_from_bit3: assert property (
        @(posedge clk) Cout == (
            (A[3] & B[3]) |
            ((A[3] ^ B[3]) & (
                (A[2] & B[2]) |
                ((A[2] ^ B[2]) & (
                    (A[1] & B[1]) |
                    ((A[1] ^ B[1]) & ((A[0] & B[0]) | ((A[0] ^ B[0]) & Cin)))
                ))
            ))
        )
    );

    // The 5-bit result matches the 4-bit addition with carry-in.
    check_full_result_matches_addition: assert property (
        @(posedge clk) {Cout, S} == ({1'b0, A} + {1'b0, B} + {4'b0000, Cin})
    );

endmodule