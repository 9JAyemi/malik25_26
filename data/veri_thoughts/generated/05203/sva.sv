module four_bit_adder_sva(
    input logic       clk,
    input logic [3:0] S,
    input logic       C_out,
    input logic [3:0] A,
    input logic [3:0] B
);

    // S[0] is the XOR of the first two input XOR terms.
    check_s0_equation: assert property (
        @(posedge clk)
        S[0] == ((A[0] ^ B[0]) ^ (A[1] ^ B[1]))
    );

    // S[1] is the XOR of the upper two input XOR terms.
    check_s1_equation: assert property (
        @(posedge clk)
        S[1] == ((A[2] ^ B[2]) ^ (A[3] ^ B[3]))
    );

    // S[2] is the XOR of the middle input XOR terms.
    check_s2_equation: assert property (
        @(posedge clk)
        S[2] == ((A[1] ^ B[1]) ^ (A[2] ^ B[2]))
    );

    // S[3] matches the final XOR of S[2] and the first AND term.
    check_s3_equation: assert property (
        @(posedge clk)
        S[3] == (((A[1] ^ B[1]) ^ (A[2] ^ B[2])) ^ ((A[0] ^ B[0]) & (A[1] ^ B[1])))
    );

    // C_out matches the OR of the three carry product terms.
    check_cout_equation: assert property (
        @(posedge clk)
        C_out == (
            (((A[0] ^ B[0]) & (A[1] ^ B[1])) & ((A[2] ^ B[2]) & (A[3] ^ B[3]))) |
            (((A[1] ^ B[1]) & (A[2] ^ B[2])) & ((A[0] ^ B[0]) & (A[1] ^ B[1]))) |
            (((A[2] ^ B[2]) & (A[3] ^ B[3])) & ((A[1] ^ B[1]) & (A[2] ^ B[2])))
        )
    );

    // Equal inputs drive all XOR-derived outputs low.
    check_equal_inputs_zero_outputs: assert property (
        @(posedge clk)
        (A == B) |-> ((S == 4'b0000) && (C_out == 1'b0))
    );

    // Any carry-out requires both middle XOR terms to be high.
    check_cout_requires_middle_terms: assert property (
        @(posedge clk)
        C_out |-> ((A[1] ^ B[1]) & (A[2] ^ B[2]))
    );

endmodule