module four_to_one_sva (
    input logic clk,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic X
);

    // X matches the implemented sum-of-products function.
    check_functional_equivalence: assert property (
        @(posedge clk)
        X == (((~(A1 | A2)) & (~(B1 | B2))) | ((A1 & A2) & (B1 & B2)))
    );

    // All four inputs low drives X high.
    check_all_low_sets_x: assert property (
        @(posedge clk)
        ((!A1 && !A2) && (!B1 && !B2)) |-> X
    );

    // All four inputs high drives X high.
    check_all_high_sets_x: assert property (
        @(posedge clk)
        ((A1 && A2) && (B1 && B2)) |-> X
    );

    // A mixed pair cannot produce X high.
    check_mixed_a_clears_x: assert property (
        @(posedge clk)
        (A1 ^ A2) |-> !X
    );

    // B mixed pair cannot produce X high.
    check_mixed_b_clears_x: assert property (
        @(posedge clk)
        (B1 ^ B2) |-> !X
    );

    // A low pair with B high pair drives X low.
    check_a_low_b_high_clears_x: assert property (
        @(posedge clk)
        ((!A1 && !A2) && (B1 && B2)) |-> !X
    );

    // A high pair with B low pair drives X low.
    check_a_high_b_low_clears_x: assert property (
        @(posedge clk)
        ((A1 && A2) && (!B1 && !B2)) |-> !X
    );

    // X can only be high for matching all-low or all-high pairs.
    check_x_high_only_on_matching_extremes: assert property (
        @(posedge clk)
        X |-> (((!A1 && !A2) && (!B1 && !B2)) || ((A1 && A2) && (B1 && B2)))
    );

endmodule