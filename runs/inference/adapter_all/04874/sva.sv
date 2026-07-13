module and_gate_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic Y
);

    // Y must equal the AND of A, B, and C.
    check_y_matches_and: assert property (
        @(posedge clk) Y == (A & B & C)
    );

    // If Y is high, all inputs must be high.
    check_y_high_requires_all_inputs_high: assert property (
        @(posedge clk) Y |-> (A && B && C)
    );

    // If A is low, Y must be low.
    check_a_low_forces_y_low: assert property (
        @(posedge clk) !A |-> !Y
    );

    // If B is low, Y must be low.
    check_b_low_forces_y_low: assert property (
        @(posedge clk) !B |-> !Y
    );

    // If C is low, Y must be low.
    check_c_low_forces_y_low: assert property (
        @(posedge clk) !C |-> !Y
    );

    // If all inputs are high, Y must be high.
    check_all_inputs_high_sets_y: assert property (
        @(posedge clk) (A && B && C) |-> Y
    );

endmodule