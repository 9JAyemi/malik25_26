module four_input_and_sva (
    input logic clk,
    input logic A1,
    input logic A2,
    input logic B1_N,
    input logic C1,
    input logic X
);

    // X must match the implemented AND-with-inverted-B function.
    check_x_matches_function: assert property (
        @(posedge clk) X == (A1 & A2 & ~B1_N)
    );

    // All three active inputs must drive X high.
    check_all_active_inputs_drive_x: assert property (
        @(posedge clk) (A1 && A2 && !B1_N) |-> X
    );

    // A low A1 forces X low.
    check_a1_low_forces_x_low: assert property (
        @(posedge clk) !A1 |-> !X
    );

    // A low A2 forces X low.
    check_a2_low_forces_x_low: assert property (
        @(posedge clk) !A2 |-> !X
    );

    // A high B1_N forces X low.
    check_b1n_high_forces_x_low: assert property (
        @(posedge clk) B1_N |-> !X
    );

    // With B1_N low, X reduces to A1 AND A2.
    check_b1n_low_reduces_to_and: assert property (
        @(posedge clk) !B1_N |-> (X == (A1 & A2))
    );

    // With A1 and A2 high, X reduces to inverted B1_N.
    check_a1_a2_high_reduces_to_not_b1n: assert property (
        @(posedge clk) (A1 && A2) |-> (X == !B1_N)
    );

    // With A1 and A2 low, X must be low regardless of B1_N.
    check_a1_a2_low_force_x_low: assert property (
        @(posedge clk) (!A1 && !A2) |-> !X
    );

    // With B1_N high, X must be low regardless of A1 and A2.
    check_b1n_high_force_x_low: assert property (
        @(posedge clk) B1_N |-> !X
    );

endmodule