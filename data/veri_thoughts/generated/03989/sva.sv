module three_input_gate_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic X
);

    // No clock or reset in the DUT; sample combinational behavior on the global clock.

    // X must match the exact RTL equation.
    check_output_matches_rtl_equation: assert property (
        @($global_clock)
        X == ((A1 & ~A2) | (~A1 & A2) | (~B1 & ~(A1 & A2 & B1)))
    );

    // X is equivalent to XOR(A1,A2) OR NOT(B1).
    check_output_matches_simplified_equation: assert property (
        @($global_clock)
        X == ((A1 ^ A2) | ~B1)
    );

    // A low B1 forces X high.
    check_b1_low_forces_x_high: assert property (
        @($global_clock)
        (!B1) |-> X
    );

    // Different A inputs force X high.
    check_a_inputs_mismatch_forces_x_high: assert property (
        @($global_clock)
        (A1 ^ A2) |-> X
    );

    // With B1 high, X reduces to A1 XOR A2.
    check_b1_high_reduces_to_xor: assert property (
        @($global_clock)
        B1 |-> (X == (A1 ^ A2))
    );

    // With B1 high and equal A inputs, X must be low.
    check_b1_high_equal_a_inputs_force_x_low: assert property (
        @($global_clock)
        (B1 && (A1 == A2)) |-> (!X)
    );

endmodule