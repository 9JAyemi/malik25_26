module sky130_fd_sc_ms__fahcon_sva (
    input logic clk,
    input logic COUT_N,
    input logic SUM,
    input logic A,
    input logic B,
    input logic CI
);

    // SUM implements three-input XOR of A, B, CI.
    check_sum_xor3: assert property (
        @(posedge clk) SUM == (A ^ B ^ CI)
    );

    // COUT_N is the inverse of the majority function of A, B, CI.
    check_coutn_inverse_majority: assert property (
        @(posedge clk) COUT_N == ~((A & B) | (A & CI) | (B & CI))
    );

    // When A equals B, SUM equals CI.
    check_sum_when_ab_equal: assert property (
        @(posedge clk) (A == B) |-> (SUM == CI)
    );

    // When A differs from B, SUM equals inverted CI.
    check_sum_when_ab_differs: assert property (
        @(posedge clk) (A != B) |-> (SUM == ~CI)
    );

    // If both A and B are 1, COUT_N must be 0 regardless of CI.
    check_coutn_low_when_ab_11: assert property (
        @(posedge clk) (A & B) |-> (COUT_N == 1'b0)
    );

    // If both A and B are 0, COUT_N must be 1 regardless of CI.
    check_coutn_high_when_ab_00: assert property (
        @(posedge clk) (~A & ~B) |-> (COUT_N == 1'b1)
    );

    // For input vector 000, SUM=0 and COUT_N=1.
    check_vector_000: assert property (
        @(posedge clk) (A == 1'b0 && B == 1'b0 && CI == 1'b0) |-> (SUM == 1'b0 && COUT_N == 1'b1)
    );

    // For input vector 111, SUM=1 and COUT_N=0.
    check_vector_111: assert property (
        @(posedge clk) (A == 1'b1 && B == 1'b1 && CI == 1'b1) |-> (SUM == 1'b1 && COUT_N == 1'b0)
    );

    // SUM toggles iff an odd number of inputs (A,B,CI) change between cycles.
    check_sum_toggles_on_odd_change: assert property (
        @(posedge clk) ($changed(A) ^ $changed(B) ^ $changed(CI)) |-> $changed(SUM)
    );

    // SUM stays stable if an even number of inputs (including zero) change between cycles.
    check_sum_stable_on_even_change: assert property (
        @(posedge clk) ~($changed(A) ^ $changed(B) ^ $changed(CI)) |-> !$changed(SUM)
    );

endmodule