module MUXCY_sva (
    input logic clk,
    input logic O,
    input logic CO,
    input logic CI,
    input logic DI,
    input logic S,
    input logic CIN
);

    // O matches the implemented sum equation.
    check_o_matches_sum_equation: assert property (
        @(posedge clk) O == ((S & DI) | (~S & CI))
    );

    // CO matches the implemented carry equation.
    check_co_matches_carry_equation: assert property (
        @(posedge clk) CO == (((CI & S) | (DI & (CI | S))))
    );

    // When S is low, O follows CI.
    check_o_follows_ci_when_s_low: assert property (
        @(posedge clk) !S |-> (O == CI)
    );

    // When S is high, O follows DI.
    check_o_follows_di_when_s_high: assert property (
        @(posedge clk) S |-> (O == DI)
    );

    // When S is low, CO follows CIN.
    check_co_follows_cin_when_s_low: assert property (
        @(posedge clk) !S |-> (CO == CIN)
    );

    // When S is high, CO follows DI.
    check_co_follows_di_when_s_high: assert property (
        @(posedge clk) S |-> (CO == DI)
    );

    // With S low and CI low, O is low.
    check_o_low_when_s_low_and_ci_low: assert property (
        @(posedge clk) (!S && !CI) |-> !O
    );

    // With S low and CI high, O is high.
    check_o_high_when_s_low_and_ci_high: assert property (
        @(posedge clk) (!S && CI) |-> O
    );

    // With S high and DI low, O is low.
    check_o_low_when_s_high_and_di_low: assert property (
        @(posedge clk) (S && !DI) |-> !O
    );

    // With S high and DI high, O is high.
    check_o_high_when_s_high_and_di_high: assert property (
        @(posedge clk) (S && DI) |-> O
    );

endmodule