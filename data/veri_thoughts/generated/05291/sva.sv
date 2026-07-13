module FA_106_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic Ci,
    input logic S,
    input logic Co
);

    // Sum matches the three-input parity function.
    check_sum_matches_xor: assert property (
        @(posedge clk) S == (A ^ B ^ Ci)
    );

    // Carry matches the AND of A and B.
    check_carry_matches_ab_and: assert property (
        @(posedge clk) Co == (A & B)
    );

    // Equal A and B make the sum follow Ci.
    check_sum_follows_cin_when_ab_equal: assert property (
        @(posedge clk) (A == B) |-> (S == Ci)
    );

    // Different A and B make the sum invert Ci.
    check_sum_inverts_cin_when_ab_different: assert property (
        @(posedge clk) (A ^ B) |-> (S == ~Ci)
    );

    // A low forces carry low.
    check_carry_low_when_a_low: assert property (
        @(posedge clk) (A == 1'b0) |-> (Co == 1'b0)
    );

    // B low forces carry low.
    check_carry_low_when_b_low: assert property (
        @(posedge clk) (B == 1'b0) |-> (Co == 1'b0)
    );

    // A and B high force carry high.
    check_carry_high_when_ab_high: assert property (
        @(posedge clk) ((A == 1'b1) && (B == 1'b1)) |-> (Co == 1'b1)
    );

    // High carry implies the sum equals Ci.
    check_sum_matches_cin_when_carry_high: assert property (
        @(posedge clk) (Co == 1'b1) |-> (S == Ci)
    );

endmodule