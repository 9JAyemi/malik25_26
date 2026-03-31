module mult_select_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1_N
);

    // X matches the RTL Boolean equation.
    check_x_matches_rtl_equation: assert property (
        @(posedge clk)
        X == ((A1 & A2 & ~B1_N) | (~A1 & (A2 | B1_N)))
    );

    // When A1 is high, X reduces to A2.
    check_a1_high_selects_a2: assert property (
        @(posedge clk)
        A1 |-> (X == A2)
    );

    // When A1 is low, X reduces to B1_N OR A2.
    check_a1_low_selects_b1n_or_a2: assert property (
        @(posedge clk)
        !A1 |-> (X == (B1_N | A2))
    );

    // When A2 is low, X reduces to B1_N.
    check_a2_low_selects_b1n: assert property (
        @(posedge clk)
        !A2 |-> (X == B1_N)
    );

    // When A2 is high, X is always high.
    check_a2_high_forces_x_high: assert property (
        @(posedge clk)
        A2 |-> (X == 1'b1)
    );

    // When B1_N is high, X reduces to A2.
    check_b1n_high_selects_a2: assert property (
        @(posedge clk)
        B1_N |-> (X == A2)
    );

    // When B1_N is low, X reduces to A1 OR A2.
    check_b1n_low_selects_a1_or_a2: assert property (
        @(posedge clk)
        !B1_N |-> (X == (A1 | A2))
    );

endmodule