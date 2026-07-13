module full_adder_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic CI,
    input logic SUM,
    input logic COUT
);

    // SUM matches the three-input parity bit.
    check_sum_parity: assert property (
        @(posedge clk) SUM == (A ^ B ^ CI)
    );

    // COUT matches the implemented top-level logic.
    check_cout_function: assert property (
        @(posedge clk) COUT == (CI && !A && !B)
    );

    // All-zero inputs produce zero outputs.
    check_zero_case: assert property (
        @(posedge clk) (!A && !B && !CI) |-> (!SUM && !COUT)
    );

    // Only CI high produces both outputs high.
    check_ci_only_case: assert property (
        @(posedge clk) (!A && !B && CI) |-> (SUM && COUT)
    );

    // CI low forces COUT low.
    check_ci_low_blocks_cout: assert property (
        @(posedge clk) !CI |-> !COUT
    );

    // Any asserted A or B forces COUT low.
    check_ab_high_blocks_cout: assert property (
        @(posedge clk) (A || B) |-> !COUT
    );

endmodule