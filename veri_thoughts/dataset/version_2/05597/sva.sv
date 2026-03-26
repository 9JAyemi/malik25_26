module or4b_2_sva (
    input logic X,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic VPWR,
    input logic VGND
);

    // No explicit clock or reset exists in the RTL; sample on the formal global clock.

    // X must always equal the OR of A, B, C, and D.
    check_or_equivalence: assert property (
        @($global_clock) X == (A | B | C | D)
    );

    // X must be low when all four inputs are low.
    check_all_low_drives_low: assert property (
        @($global_clock)
        ((A == 1'b0) && (B == 1'b0) && (C == 1'b0) && (D == 1'b0)) |-> (X == 1'b0)
    );

    // A high must drive X high.
    check_a_high_drives_high: assert property (
        @($global_clock) (A == 1'b1) |-> (X == 1'b1)
    );

    // B high must drive X high.
    check_b_high_drives_high: assert property (
        @($global_clock) (B == 1'b1) |-> (X == 1'b1)
    );

    // C high must drive X high.
    check_c_high_drives_high: assert property (
        @($global_clock) (C == 1'b1) |-> (X == 1'b1)
    );

    // D high must drive X high.
    check_d_high_drives_high: assert property (
        @($global_clock) (D == 1'b1) |-> (X == 1'b1)
    );

    // If X is low, then all four inputs must be low.
    check_x_low_implies_all_low: assert property (
        @($global_clock)
        (X == 1'b0) |-> ((A == 1'b0) && (B == 1'b0) && (C == 1'b0) && (D == 1'b0))
    );

endmodule