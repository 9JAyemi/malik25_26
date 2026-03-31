module my_module_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1
);

// Y matches the implemented OR-AND-NOT function.
    check_y_matches_function: assert property (
        @(posedge clk) Y == ~(A1 | A2 | B1 | C1)
    );

// A high on A1 forces Y low.
    check_a1_high_forces_y_low: assert property (
        @(posedge clk) A1 |-> !Y
    );

// A high on A2 forces Y low.
    check_a2_high_forces_y_low: assert property (
        @(posedge clk) A2 |-> !Y
    );

// A high on B1 forces Y low.
    check_b1_high_forces_y_low: assert property (
        @(posedge clk) B1 |-> !Y
    );

// A high on C1 forces Y low.
    check_c1_high_forces_y_low: assert property (
        @(posedge clk) C1 |-> !Y
    );

// All four high inputs force Y low.
    check_all_inputs_high_force_y_low: assert property (
        @(posedge clk) (A1 && A2 && B1 && C1) |-> !Y
    );

// A low Y requires at least one high input.
    check_y_low_requires_some_input_high: assert property (
        @(posedge clk) !Y |-> (A1 || A2 || B1 || C1)
    );

// A high Y requires all four inputs low.
    check_y_high_requires_all_inputs_low: assert property (
        @(posedge clk) Y |-> (!A1 && !A2 && !B1 && !C1)
    );

endmodule
