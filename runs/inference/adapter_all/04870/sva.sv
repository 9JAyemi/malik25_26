module logical_and_sva (
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

    // If any input is low, Y must be low.
    check_any_input_low_forces_y_low: assert property (
        @(posedge clk) (!A || !B || !C) |-> !Y
    );

    // If all inputs are high, Y must be high.
    check_all_inputs_high_forces_y_high: assert property (
        @(posedge clk) (A && B && C) |-> Y
    );

endmodule