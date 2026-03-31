module digital_circuit_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1_N
);

// Y matches the implemented NOT/NOR/AND logic.
    check_y_matches_implemented_logic: assert property (
        @(posedge clk) Y == ~((~B1_N) | (A1 & A2))
    );

// A high B1_N forces Y high.
    check_b1n_high_forces_y_high: assert property (
        @(posedge clk) B1_N |-> Y
    );

// A low B1_N with both A inputs low forces Y high.
    check_b1n_low_and_a_inputs_low_force_y_high: assert property (
        @(posedge clk) (!B1_N && !A1 && !A2) |-> Y
    );

// A low B1_N with any A input high forces Y low.
    check_b1n_low_and_any_a_high_forces_y_low: assert property (
        @(posedge clk) (!B1_N && (A1 || A2)) |-> !Y
    );

// A high Y requires B1_N high and both A inputs low.
    check_y_high_requires_b1n_and_a_inputs_low: assert property (
        @(posedge clk) Y |-> (B1_N && !A1 && !A2)
    );

// A low Y requires B1_N low and at least one A input high.
    check_y_low_requires_b1n_low_and_any_a_high: assert property (
        @(posedge clk) !Y |-> (!B1_N && (A1 || A2))
    );

endmodule
