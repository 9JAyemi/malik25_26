module full_adder_sva (
    input logic A,
    input logic B,
    input logic CI,
    input logic SUM,
    input logic COUT_N
);
    // No clock/reset in DUT; combinational logic; sample on any input edge.

    // SUM equals three-input XOR of A, B, and CI.
    check_sum_is_three_input_xor: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge CI or negedge CI)
            SUM == (A ^ B ^ CI)
    );

    // COUT_N is the inverse of majority(A,B,CI) = ~(A&B | A&CI | B&CI).
    check_coutn_is_not_majority: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge CI or negedge CI)
            COUT_N == ~((A & B) | (A & CI) | (B & CI))
    );

    // When any two inputs are 1, COUT_N must be 0.
    check_carry_low_when_two_ones: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge CI or negedge CI)
            ((A & B) | (A & CI) | (B & CI)) |-> (COUT_N == 1'b0)
    );

    // When at most one input is 1, COUT_N must be 1.
    check_carry_high_when_zero_or_one_one: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge CI or negedge CI)
            ((~A & ~B) | (~A & ~CI) | (~B & ~CI)) |-> (COUT_N == 1'b1)
    );

    // If A equals B, SUM equals CI.
    check_sum_eq_ci_when_a_eq_b: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge CI or negedge CI)
            (A == B) |-> (SUM == CI)
    );

    // If A differs from B, SUM equals ~CI.
    check_sum_eq_not_ci_when_a_ne_b: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge CI or negedge CI)
            (A != B) |-> (SUM == ~CI)
    );

    // When all inputs are 0, SUM=0 and COUT_N=1.
    check_case_all_zero: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge CI or negedge CI)
            (~A & ~B & ~CI) |-> ((SUM == 1'b0) && (COUT_N == 1'b1))
    );

    // When exactly one input is 1, SUM=1 and COUT_N=1.
    check_case_exactly_one_one: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge CI or negedge CI)
            ((A & ~B & ~CI) | (~A & B & ~CI) | (~A & ~B & CI)) |-> ((SUM == 1'b1) && (COUT_N == 1'b1))
    );

    // When exactly two inputs are 1, SUM=0 and COUT_N=0.
    check_case_exactly_two_ones: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge CI or negedge CI)
            ((A & B & ~CI) | (A & CI & ~B) | (B & CI & ~A)) |-> ((SUM == 1'b0) && (COUT_N == 1'b0))
    );

    // When all inputs are 1, SUM=1 and COUT_N=0.
    check_case_all_one: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge CI or negedge CI)
            (A & B & CI) |-> ((SUM == 1'b1) && (COUT_N == 1'b0))
    );
endmodule