module sky130_fd_sc_lp__fahcon_sva (
    input logic clk,
    input logic COUT_N,
    input logic SUM,
    input logic A,
    input logic B,
    input logic CI
);

    // SUM is the three-input XOR of A, B, and CI.
    check_sum_parity: assert property (
        @(posedge clk) SUM == (A ^ B ^ CI)
    );

    // COUT_N matches the OR of the three pairwise NOR terms.
    check_coutn_function: assert property (
        @(posedge clk) COUT_N == (((~A) & (~B)) | ((~A) & (~CI)) | ((~B) & (~CI)))
    );

    // All-zero inputs produce SUM low and COUT_N high.
    check_all_zero_case: assert property (
        @(posedge clk) (!A && !B && !CI) |-> ((SUM == 1'b0) && (COUT_N == 1'b1))
    );

    // Any single high input produces SUM high and COUT_N high.
    check_one_high_case: assert property (
        @(posedge clk)
        (( A && !B && !CI) ||
         (!A &&  B && !CI) ||
         (!A && !B &&  CI)) |-> ((SUM == 1'b1) && (COUT_N == 1'b1))
    );

    // Any two high inputs produce SUM low and COUT_N low.
    check_two_high_case: assert property (
        @(posedge clk)
        (( A &&  B && !CI) ||
         ( A && !B &&  CI) ||
         (!A &&  B &&  CI)) |-> ((SUM == 1'b0) && (COUT_N == 1'b0))
    );

    // All-high inputs produce SUM high and COUT_N low.
    check_all_high_case: assert property (
        @(posedge clk) (A && B && CI) |-> ((SUM == 1'b1) && (COUT_N == 1'b0))
    );

endmodule