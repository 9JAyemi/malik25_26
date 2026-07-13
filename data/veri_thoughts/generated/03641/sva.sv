module four_bit_adder_sva (
    input logic        clk,
    input logic [3:0]  A,
    input logic [3:0]  B,
    input logic        C_in,
    input logic [3:0]  S,
    input logic        C_out
);

    // S[0] matches the first sum assignment.
    check_sum_bit0_equation: assert property (
        @(posedge clk) S[0] == (A[0] ^ B[0] ^ C_in)
    );

    // S[1] matches the second sum assignment.
    check_sum_bit1_equation: assert property (
        @(posedge clk) S[1] == (A[1] ^ B[1] ^ C_in)
    );

    // S[2] matches the third sum assignment.
    check_sum_bit2_equation: assert property (
        @(posedge clk) S[2] == (A[2] ^ B[2] ^ C_in)
    );

    // S[3] matches the fourth sum assignment.
    check_sum_bit3_equation: assert property (
        @(posedge clk) S[3] == (A[3] ^ B[3] ^ C_in)
    );

    // The full sum bus matches the per-bit XOR structure.
    check_sum_vector_equation: assert property (
        @(posedge clk) S == ((A ^ B) ^ {4{C_in}})
    );

    // With C_in low, S reduces to A XOR B.
    check_sum_when_cin_low: assert property (
        @(posedge clk) (C_in == 1'b0) |-> (S == (A ^ B))
    );

    // With C_in high, S is the inverse of A XOR B.
    check_sum_when_cin_high: assert property (
        @(posedge clk) (C_in == 1'b1) |-> (S == ~(A ^ B))
    );

    // C_out matches the RTL carry expression.
    check_cout_equation: assert property (
        @(posedge clk) C_out == ((((A[0] & B[0]) & (A[1] ^ B[1])) | (A[1] & B[1])))
    );

    // A generate on bit 1 forces C_out high.
    check_cout_from_bit1_generate: assert property (
        @(posedge clk) (A[1] & B[1]) |-> (C_out == 1'b1)
    );

    // The lower carry-propagate term forces C_out high.
    check_cout_from_low_propagate: assert property (
        @(posedge clk) ((A[0] & B[0]) & (A[1] ^ B[1])) |-> (C_out == 1'b1)
    );

    // If neither carry term is present, C_out stays low.
    check_cout_low_when_no_carry_term: assert property (
        @(posedge clk) (!(A[1] & B[1]) && !((A[0] & B[0]) & (A[1] ^ B[1]))) |-> (C_out == 1'b0)
    );

endmodule