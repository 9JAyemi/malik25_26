module three_to_one_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic Y
);

    // Y must equal the implemented OR-of-products function.
    check_y_matches_function: assert property (
        @($global_clock) Y == ((A1 & A2) | B1)
    );

    // B1 high must force Y high.
    check_b1_forces_y_high: assert property (
        @($global_clock) B1 |-> Y
    );

    // A1 and A2 high together must force Y high.
    check_a1_a2_force_y_high: assert property (
        @($global_clock) (A1 & A2) |-> Y
    );

    // With B1 low, Y must reduce to A1 OR A2.
    check_b1_low_reduces_to_a1_or_a2: assert property (
        @($global_clock) !B1 |-> (Y == (A1 | A2))
    );

    // With A1 and A2 low, Y must follow B1.
    check_a1_a2_low_follows_b1: assert property (
        @($global_clock) (!A1 & !A2) |-> (Y == B1)
    );

endmodule