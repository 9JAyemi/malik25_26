module digital_circuit_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1_N
);

    // Y matches the implemented NOT-AND-NOR function.
    check_y_function: assert property (
        @(posedge clk) Y == ~((~B1_N) | (A1 & A2))
    );

    // A low B1_N forces the NOR output low.
    check_b1n_low_forces_y_low: assert property (
        @(posedge clk) !B1_N |-> !Y
    );

    // High A1 and A2 force the AND term high and drive Y low.
    check_a1_a2_high_force_y_low: assert property (
        @(posedge clk) (A1 && A2) |-> !Y
    );

    // With B1_N high and either A1 or A2 low, Y is high.
    check_b1n_high_and_any_a_low_force_y_high: assert property (
        @(posedge clk) (B1_N && (!A1 || !A2)) |-> Y
    );

    // A high Y requires B1_N high and the AND term low.
    check_y_high_requires_b1n_and_and_term_low: assert property (
        @(posedge clk) Y |-> (B1_N && !(A1 && A2))
    );

    // A low Y requires B1_N low or the AND term high.
    check_y_low_requires_b1n_low_or_and_term_high: assert property (
        @(posedge clk) !Y |-> (!B1_N || (A1 && A2))
    );

endmodule