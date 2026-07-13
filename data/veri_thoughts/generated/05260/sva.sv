module full_adder_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic CI,
    input logic SUM,
    input logic COUT
);

    // SUM must match the XOR of A, B, and CI.
    check_sum_equation: assert property (
        @(posedge clk) SUM == (A ^ B ^ CI)
    );

    // COUT must match the implemented carry equation.
    check_cout_equation: assert property (
        @(posedge clk) COUT == ((A & B) | ((A ^ B) & CI))
    );

    // All-zero input must produce zero sum and zero carry.
    check_all_zero_case: assert property (
        @(posedge clk) (!A && !B && !CI) |-> (!SUM && !COUT)
    );

    // Exactly one high input must produce sum one and carry zero.
    check_single_one_case: assert property (
        @(posedge clk)
        (( A && !B && !CI) ||
         (!A &&  B && !CI) ||
         (!A && !B &&  CI)) |-> (SUM && !COUT)
    );

    // Exactly two high inputs must produce sum zero and carry one.
    check_double_one_case: assert property (
        @(posedge clk)
        (( A &&  B && !CI) ||
         ( A && !B &&  CI) ||
         (!A &&  B &&  CI)) |-> (!SUM && COUT)
    );

    // All-one input must produce sum one and carry one.
    check_all_one_case: assert property (
        @(posedge clk) (A && B && CI) |-> (SUM && COUT)
    );

endmodule