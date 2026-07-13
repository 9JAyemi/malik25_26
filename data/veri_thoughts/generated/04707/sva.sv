module sky130_fd_sc_ls__fahcon_sva (
    input logic COUT_N,
    input logic SUM,
    input logic A,
    input logic B,
    input logic CI
);

    // SUM matches the 3-input XOR of A, B, and CI.
    check_sum_function: assert property (
        @($global_clock) SUM == (A ^ B ^ CI)
    );

    // COUT_N matches the OR of the three pairwise NOR terms.
    check_coutn_function: assert property (
        @($global_clock) COUT_N == ((~A & ~B) | (~A & ~CI) | (~B & ~CI))
    );

    // COUT_N is the inverted full-adder carry output.
    check_coutn_inverted_carry: assert property (
        @($global_clock) (~COUT_N) == ((A & B) | (A & CI) | (B & CI))
    );

    // All-low inputs produce SUM low and COUT_N high.
    check_all_low_case: assert property (
        @($global_clock) (!A && !B && !CI) |-> (SUM == 1'b0 && COUT_N == 1'b1)
    );

    // Any one-hot input combination produces SUM high and COUT_N high.
    check_one_hot_case: assert property (
        @($global_clock)
        (( A && !B && !CI) ||
         (!A &&  B && !CI) ||
         (!A && !B &&  CI)) |-> (SUM == 1'b1 && COUT_N == 1'b1)
    );

    // Any two-hot input combination produces SUM low and COUT_N low.
    check_two_hot_case: assert property (
        @($global_clock)
        (( A &&  B && !CI) ||
         ( A && !B &&  CI) ||
         (!A &&  B &&  CI)) |-> (SUM == 1'b0 && COUT_N == 1'b0)
    );

    // All-high inputs produce SUM high and COUT_N low.
    check_all_high_case: assert property (
        @($global_clock) (A && B && CI) |-> (SUM == 1'b1 && COUT_N == 1'b0)
    );

endmodule