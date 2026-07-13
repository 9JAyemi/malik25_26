module five_to_one_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic D1
);

    // No explicit clock or reset; sample this combinational DUT on the formal global clock.

    // X must match the implemented combinational equation.
    check_function_match: assert property (
        @($global_clock) disable iff ($initstate)
        X == (D1 ? ((A1 & A2) | (B1 & ~C1)) : 1'b0)
    );

    // When D1 is low, X must be low.
    check_d1_low_forces_zero: assert property (
        @($global_clock) disable iff ($initstate)
        !D1 |-> (X == 1'b0)
    );

    // When D1 is high, X must equal the selected logic expression.
    check_d1_high_selects_logic: assert property (
        @($global_clock) disable iff ($initstate)
        D1 |-> (X == ((A1 & A2) | (B1 & ~C1)))
    );

    // The A1/A2 term is sufficient to drive X high.
    check_a_term_drives_high: assert property (
        @($global_clock) disable iff ($initstate)
        (D1 && A1 && A2) |-> (X == 1'b1)
    );

    // The B1/~C1 term is sufficient to drive X high.
    check_b_term_drives_high: assert property (
        @($global_clock) disable iff ($initstate)
        (D1 && B1 && ~C1) |-> (X == 1'b1)
    );

    // With D1 high and both terms false, X must be low.
    check_no_term_drives_low: assert property (
        @($global_clock) disable iff ($initstate)
        (D1 && !((A1 & A2) | (B1 & ~C1))) |-> (X == 1'b0)
    );

endmodule