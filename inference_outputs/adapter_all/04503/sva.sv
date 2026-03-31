module sky130_fd_sc_hd__fah_sva (
    input logic clk,
    input logic COUT,
    input logic SUM,
    input logic A,
    input logic B,
    input logic CI
);

    // SUM is the XOR of A, B, and CI.
    check_sum_xor: assert property (
        @(posedge clk) SUM == (A ^ B ^ CI)
    );

    // COUT is high when at least two inputs are high.
    check_cout_majority: assert property (
        @(posedge clk) COUT == ((A & B) | (A & CI) | (B & CI))
    );

    // All-zero inputs produce zero sum and zero carry.
    check_all_zero_case: assert property (
        @(posedge clk) (!A && !B && !CI) |-> (!SUM && !COUT)
    );

    // All-one inputs produce sum one and carry one.
    check_all_one_case: assert property (
        @(posedge clk) (A && B && CI) |-> (SUM && COUT)
    );

    // Exactly one high input produces sum one and carry zero.
    check_one_hot_case: assert property (
        @(posedge clk)
        ((A && !B && !CI) || (!A && B && !CI) || (!A && !B && CI))
        |-> (SUM && !COUT)
    );

    // Exactly two high inputs produce sum zero and carry one.
    check_two_hot_case: assert property (
        @(posedge clk)
        ((A && B && !CI) || (A && !B && CI) || (!A && B && CI))
        |-> (!SUM && COUT)
    );

endmodule