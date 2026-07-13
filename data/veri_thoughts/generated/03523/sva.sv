module full_adder_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic Ci,
    input logic S,
    input logic Co
);

    // Combinational DUT sampled on clk; no reset is present in the RTL.

    // Sum output implements three-input XOR.
    check_sum_matches_three_input_xor: assert property (
        @(posedge clk) S == (A ^ B ^ Ci)
    );

    // Carry output is asserted only by A and B both being high.
    check_carry_matches_ab_and: assert property (
        @(posedge clk) Co == (A & B)
    );

    // With Ci low, sum reduces to A xor B.
    check_sum_when_cin_low: assert property (
        @(posedge clk) (!Ci) |-> (S == (A ^ B))
    );

    // With Ci high, sum is the inversion of A xor B.
    check_sum_when_cin_high: assert property (
        @(posedge clk) Ci |-> (S == ~(A ^ B))
    );

    // When A and B are equal, sum follows Ci.
    check_sum_tracks_cin_when_ab_equal: assert property (
        @(posedge clk) (A == B) |-> (S == Ci)
    );

    // When A and B differ, sum is the inverse of Ci.
    check_sum_inverts_cin_when_ab_different: assert property (
        @(posedge clk) (A != B) |-> (S == ~Ci)
    );

    // Carry must be high whenever both A and B are high.
    check_carry_high_when_ab_high: assert property (
        @(posedge clk) (A && B) |-> Co
    );

    // Carry must be low whenever either A or B is low.
    check_carry_low_when_either_operand_low: assert property (
        @(posedge clk) ((!A) || (!B)) |-> (!Co)
    );

endmodule