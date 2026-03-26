module sky130_fd_sc_ls__fah_sva (
    input logic clk,
    input logic COUT,
    input logic SUM,
    input logic A,
    input logic B,
    input logic CI
);

    // SUM matches the three-input XOR of A, B, and CI.
    check_sum_function: assert property (
        @(posedge clk) SUM == (A ^ B ^ CI)
    );

    // COUT matches the majority function of A, B, and CI.
    check_cout_function: assert property (
        @(posedge clk) COUT == ((A & B) | (A & CI) | (B & CI))
    );

    // All-zero inputs produce zero sum and no carry.
    check_zero_inputs_result_zero: assert property (
        @(posedge clk) (!A && !B && !CI) |-> (SUM == 1'b0 && COUT == 1'b0)
    );

    // Exactly one high input produces sum without carry.
    check_one_hot_inputs_result_sum_only: assert property (
        @(posedge clk)
        ((A && !B && !CI) || (!A && B && !CI) || (!A && !B && CI))
        |-> (SUM == 1'b1 && COUT == 1'b0)
    );

    // Exactly two high inputs produce carry without sum.
    check_two_hot_inputs_result_carry_only: assert property (
        @(posedge clk)
        ((A && B && !CI) || (A && !B && CI) || (!A && B && CI))
        |-> (SUM == 1'b0 && COUT == 1'b1)
    );

    // All-high inputs produce both sum and carry.
    check_all_inputs_high_result_sum_and_carry: assert property (
        @(posedge clk) (A && B && CI) |-> (SUM == 1'b1 && COUT == 1'b1)
    );

endmodule