module four_bit_adder_sva (
    input logic        clk,
    input logic [3:0]  A,
    input logic [3:0]  B,
    input logic        CIN,
    input logic [3:0]  S,
    input logic        COUT
);

    // Full 5-bit result must match A + B + CIN.
    check_full_sum_matches: assert property (
        @(posedge clk) {COUT, S} == ({1'b0, A} + {1'b0, B} + CIN)
    );

    // Bit 0 sum must implement the first full-adder XOR.
    check_bit0_sum_xor: assert property (
        @(posedge clk) S[0] == (A[0] ^ B[0] ^ CIN)
    );

    // Zero inputs with no carry-in must produce zero.
    check_zero_inputs: assert property (
        @(posedge clk) (A == 4'b0000 && B == 4'b0000 && CIN == 1'b0) |-> (S == 4'b0000 && COUT == 1'b0)
    );

    // Zero inputs with carry-in must produce one.
    check_zero_inputs_with_cin: assert property (
        @(posedge clk) (A == 4'b0000 && B == 4'b0000 && CIN == 1'b1) |-> (S == 4'b0001 && COUT == 1'b0)
    );

    // With B and CIN low, the output must pass through A.
    check_addition_identity_a: assert property (
        @(posedge clk) (B == 4'b0000 && CIN == 1'b0) |-> (S == A && COUT == 1'b0)
    );

    // With A and CIN low, the output must pass through B.
    check_addition_identity_b: assert property (
        @(posedge clk) (A == 4'b0000 && CIN == 1'b0) |-> (S == B && COUT == 1'b0)
    );

    // Arithmetic overflow must raise COUT.
    check_overflow_sets_cout: assert property (
        @(posedge clk) (({1'b0, A} + {1'b0, B} + CIN) > 5'd15) |-> (COUT == 1'b1)
    );

    // No arithmetic overflow must keep COUT low.
    check_no_overflow_clears_cout: assert property (
        @(posedge clk) (({1'b0, A} + {1'b0, B} + CIN) <= 5'd15) |-> (COUT == 1'b0)
    );

    // 15 plus carry-in must wrap to zero with carry-out.
    check_f_plus_cin_wraps: assert property (
        @(posedge clk) (A == 4'hF && B == 4'h0 && CIN == 1'b1) |-> (S == 4'h0 && COUT == 1'b1)
    );

    // Maximum operands with carry-in must produce 5'h1F.
    check_max_operands_case: assert property (
        @(posedge clk) (A == 4'hF && B == 4'hF && CIN == 1'b1) |-> ({COUT, S} == 5'h1F)
    );

endmodule