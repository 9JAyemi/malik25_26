module three_input_gate_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic Y
);

    // No RTL clock or reset; sample combinational behavior on clk.

    // Y matches the RTL pairwise-AND OR function.
    check_majority_equation: assert property (
        @(posedge clk) Y == ((A & B) | (A & C) | (B & C))
    );

    // A and B high must drive Y high.
    check_ab_pair_sets_y: assert property (
        @(posedge clk) (A & B) |-> Y
    );

    // A and C high must drive Y high.
    check_ac_pair_sets_y: assert property (
        @(posedge clk) (A & C) |-> Y
    );

    // B and C high must drive Y high.
    check_bc_pair_sets_y: assert property (
        @(posedge clk) (B & C) |-> Y
    );

    // With A low, Y high requires B and C high.
    check_y_with_a_low_requires_bc: assert property (
        @(posedge clk) (Y & ~A) |-> (B & C)
    );

    // With B low, Y high requires A and C high.
    check_y_with_b_low_requires_ac: assert property (
        @(posedge clk) (Y & ~B) |-> (A & C)
    );

    // With C low, Y high requires A and B high.
    check_y_with_c_low_requires_ab: assert property (
        @(posedge clk) (Y & ~C) |-> (A & B)
    );

    // Zero or one high input must keep Y low.
    check_zero_or_single_high_keeps_y_low: assert property (
        @(posedge clk)
        ((~A & ~B & ~C) |
         ( A & ~B & ~C) |
         (~A &  B & ~C) |
         (~A & ~B &  C)) |-> ~Y
    );

endmodule