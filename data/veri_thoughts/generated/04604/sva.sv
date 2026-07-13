module nor4_gate_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic Y
);

    // Output equals the 4-input NOR of A, B, C, and D.
    check_nor_function: assert property (
        @(posedge clk) Y == ~(A | B | C | D)
    );

    // If all inputs are low, the output must be high.
    check_all_inputs_low_gives_high: assert property (
        @(posedge clk) (!A && !B && !C && !D) |-> Y
    );

    // A high input forces the output low.
    check_a_high_forces_low: assert property (
        @(posedge clk) A |-> !Y
    );

    // B high input forces the output low.
    check_b_high_forces_low: assert property (
        @(posedge clk) B |-> !Y
    );

    // C high input forces the output low.
    check_c_high_forces_low: assert property (
        @(posedge clk) C |-> !Y
    );

    // D high input forces the output low.
    check_d_high_forces_low: assert property (
        @(posedge clk) D |-> !Y
    );

    // A high output requires all inputs to be low.
    check_y_high_requires_all_inputs_low: assert property (
        @(posedge clk) Y |-> (!A && !B && !C && !D)
    );

    // A low output requires at least one input to be high.
    check_y_low_requires_some_input_high: assert property (
        @(posedge clk) !Y |-> (A || B || C || D)
    );

endmodule