module a31oi_2_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1
);

    // No clock or reset exists in the RTL; sample on the formal global clock.

    // Checks the exact implemented A31OI function.
    check_full_function: assert property (
        @($global_clock) Y == ~(((A1 & A2) & A3) | B1)
    );

    // B1 high forces the output low.
    check_b1_forces_low: assert property (
        @($global_clock) B1 |-> !Y
    );

    // All three A inputs high force the output low.
    check_all_a_high_forces_low: assert property (
        @($global_clock) (A1 && A2 && A3) |-> !Y
    );

    // With B1 low, the output is the inverse of the 3-input AND.
    check_b1_low_reduces_to_nand3: assert property (
        @($global_clock) (!B1) |-> (Y == ~(A1 & A2 & A3))
    );

    // If any A input is low, the output must equal ~B1.
    check_any_a_low_reduces_to_not_b1: assert property (
        @($global_clock) (!A1 || !A2 || !A3) |-> (Y == ~B1)
    );

    // B1 low and any A input low produce a high output.
    check_b1_low_and_any_a_low_yields_high: assert property (
        @($global_clock) (!B1 && (!A1 || !A2 || !A3)) |-> Y
    );

    // A high output means B1 is low and not all A inputs are high.
    check_y_high_characterization: assert property (
        @($global_clock) Y |-> (!B1 && (!A1 || !A2 || !A3))
    );

    // A low output means B1 is high or all A inputs are high.
    check_y_low_characterization: assert property (
        @($global_clock) (!Y) |-> (B1 || (A1 && A2 && A3))
    );

endmodule