module full_adder_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic CI,
    input logic SUM,
    input logic COUT
);

    // SUM must equal the three-input XOR of A, B, and CI.
    check_sum_matches_three_input_xor: assert property (
        @(posedge clk) SUM == (A ^ B ^ CI)
    );

    // COUT must equal the three-input majority function of A, B, and CI.
    check_cout_matches_three_input_majority: assert property (
        @(posedge clk) COUT == ((A & B) | (B & CI) | (CI & A))
    );

    // All-zero inputs must produce zero sum and zero carry.
    check_all_zero_case: assert property (
        @(posedge clk) (!A && !B && !CI) |-> (!SUM && !COUT)
    );

    // Exactly one high input must produce sum high and carry low.
    check_one_hot_case: assert property (
        @(posedge clk)
        ((A && !B && !CI) || (!A && B && !CI) || (!A && !B && CI))
        |-> (SUM && !COUT)
    );

    // Exactly two high inputs must produce sum low and carry high.
    check_two_hot_case: assert property (
        @(posedge clk)
        ((A && B && !CI) || (A && !B && CI) || (!A && B && CI))
        |-> (!SUM && COUT)
    );

    // All-one inputs must produce sum high and carry high.
    check_all_one_case: assert property (
        @(posedge clk) (A && B && CI) |-> (SUM && COUT)
    );

endmodule