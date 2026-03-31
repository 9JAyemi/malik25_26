module mult_select_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1_N
);

    // X must match the implemented combinational equation.
    check_x_matches_logic: assert property (
        @(posedge clk) X == ((A1 & A2 & ~B1_N) | (~A1 & (A2 | B1_N)))
    );

    // When A1 is low, X reduces to A2 OR B1_N.
    check_a1_low_branch: assert property (
        @(posedge clk) !A1 |-> (X == (A2 | B1_N))
    );

    // When A1 is high, X reduces to A2 AND inverted B1_N.
    check_a1_high_branch: assert property (
        @(posedge clk) A1 |-> (X == (A2 & ~B1_N))
    );

    // When A2 is low, X reduces to inverted B1_N.
    check_a2_low_branch: assert property (
        @(posedge clk) !A2 |-> (X == ~B1_N)
    );

    // When A2 is high, X reduces to A1 AND inverted B1_N.
    check_a2_high_branch: assert property (
        @(posedge clk) A2 |-> (X == (A1 & ~B1_N))
    );

    // When B1_N is high, X reduces to A2.
    check_b1n_high_branch: assert property (
        @(posedge clk) B1_N |-> (X == A2)
    );

    // When B1_N is low, X reduces to A1 AND A2.
    check_b1n_low_branch: assert property (
        @(posedge clk) !B1_N |-> (X == (A1 & A2))
    );

endmodule