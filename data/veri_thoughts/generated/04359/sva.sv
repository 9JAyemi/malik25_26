module nand_or_assertions (
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic X
);

    // No clock or reset exists in the RTL; sample on the formal global clock.

    // X must match the gate-level logic implemented in the RTL.
    check_structural_function: assert property (
        @($global_clock) disable iff (1'b0)
        X == ~((A | B) & ~(~(A & B) & C))
    );

    // When C is low, the logic reduces to NOR(A,B).
    check_c_low_nor_behavior: assert property (
        @($global_clock) disable iff (1'b0)
        (!C) |-> (X == ~(A | B))
    );

    // When C is high, the logic reduces to NAND(A,B).
    check_c_high_nand_behavior: assert property (
        @($global_clock) disable iff (1'b0)
        C |-> (X == ~(A & B))
    );

    // If both A and B are low, the output must be high.
    check_ab_both_low_sets_x_high: assert property (
        @($global_clock) disable iff (1'b0)
        (!A && !B) |-> (X == 1'b1)
    );

    // If both A and B are high, the output must be low.
    check_ab_both_high_sets_x_low: assert property (
        @($global_clock) disable iff (1'b0)
        (A && B) |-> (X == 1'b0)
    );

    // If A and B differ, the output must follow C.
    check_ab_different_x_matches_c: assert property (
        @($global_clock) disable iff (1'b0)
        (A ^ B) |-> (X == C)
    );

    // Holding A, B, and C constant must hold X constant, so D has no effect.
    check_output_depends_only_on_abc: assert property (
        @($global_clock) disable iff (1'b0)
        (!$initstate && $stable(A) && $stable(B) && $stable(C)) |-> $stable(X)
    );

endmodule