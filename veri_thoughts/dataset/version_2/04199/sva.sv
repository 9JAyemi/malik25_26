module Problem2_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic X
);

    // X must match the implemented sum-of-products logic.
    check_x_matches_implemented_function: assert property (
        @(posedge clk)
        X == (
            (~A & B & ~C & ~D) |
            (~A & ~B & C & D) |
            (A & D & ~B & ~C) |
            (A & B & C & ~D) |
            (~A & ~B & C & ~D) |
            (D & ~B & C) |
            (~A & B & C & D) |
            (A & ~B & C & ~D) |
            (~A & ~B & C & ~D) |
            (A & B & C & D)
        )
    );

    // Any case with B low and C high must drive X high.
    check_notb_c_forces_high: assert property (
        @(posedge clk)
        (~B & C) |-> (X == 1'b1)
    );

    // A high, B low, and D high must drive X high.
    check_a_notb_d_forces_high: assert property (
        @(posedge clk)
        (A & ~B & D) |-> (X == 1'b1)
    );

    // A, B, and C high must drive X high.
    check_abc_forces_high: assert property (
        @(posedge clk)
        (A & B & C) |-> (X == 1'b1)
    );

    // The minterm A=0, B=1, C=0, D=0 must drive X high.
    check_na_b_nc_nd_forces_high: assert property (
        @(posedge clk)
        (~A & B & ~C & ~D) |-> (X == 1'b1)
    );

    // A=0, B=0, and C=0 always produce X low.
    check_na_nb_nc_forces_low: assert property (
        @(posedge clk)
        (~A & ~B & ~C) |-> (X == 1'b0)
    );

    // B high, C low, and D high must drive X low.
    check_b_nc_d_forces_low: assert property (
        @(posedge clk)
        (B & ~C & D) |-> (X == 1'b0)
    );

    // A high, B high, and C low must drive X low.
    check_ab_nc_forces_low: assert property (
        @(posedge clk)
        (A & B & ~C) |-> (X == 1'b0)
    );

    // The minterm A=0, B=1, C=1, D=0 must drive X low.
    check_na_b_c_nd_forces_low: assert property (
        @(posedge clk)
        (~A & B & C & ~D) |-> (X == 1'b0)
    );

endmodule