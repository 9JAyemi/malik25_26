module MUX4X1_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic S0,
    input logic S1,
    input logic Z
);

    // Checks the full combinational equation for Z.
    check_full_boolean_equation: assert property (
        @(posedge clk)
        Z == (((A & ~B) & ~S1 & ~S0) |
              ((~A & B) &  S1 & ~S0) |
              ((~A & ~B) & S1 &  S0) |
              ((A & ~B) & ~S1 &  S0))
    );

    // Checks that S1 low makes Z equal A and not B.
    check_s1_low_selects_a_and_not_b: assert property (
        @(posedge clk)
        (!S1) |-> (Z == (A & ~B))
    );

    // Checks that S1 high and S0 low make Z equal not A and B.
    check_s1_high_s0_low_selects_not_a_and_b: assert property (
        @(posedge clk)
        (S1 && !S0) |-> (Z == (~A & B))
    );

    // Checks that S1 high and S0 high make Z equal not A and not B.
    check_s1_high_s0_high_selects_not_a_and_not_b: assert property (
        @(posedge clk)
        (S1 && S0) |-> (Z == (~A & ~B))
    );

    // Checks that A and B both high force Z low.
    check_ab_11_forces_zero: assert property (
        @(posedge clk)
        (A && B) |-> (Z == 1'b0)
    );

    // Checks that A high and B low make Z depend only on S1.
    check_ab_10_matches_not_s1: assert property (
        @(posedge clk)
        (A && !B) |-> (Z == (~S1))
    );

    // Checks that A low and B high produce S1 and not S0.
    check_ab_01_matches_s1_and_not_s0: assert property (
        @(posedge clk)
        (!A && B) |-> (Z == (S1 & ~S0))
    );

    // Checks that A and B both low produce S1 and S0.
    check_ab_00_matches_s1_and_s0: assert property (
        @(posedge clk)
        (!A && !B) |-> (Z == (S1 & S0))
    );

endmodule