module and_gate_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic X
);

    // Output must always equal the AND of the two inputs.
    check_output_matches_and: assert property (
        @(posedge clk) X == (A & B)
    );

    // If both inputs are high, the output must be high.
    check_both_inputs_high_drive_output_high: assert property (
        @(posedge clk) (A && B) |-> X
    );

    // If A is low, the output must be low.
    check_a_low_forces_output_low: assert property (
        @(posedge clk) !A |-> !X
    );

    // If B is low, the output must be low.
    check_b_low_forces_output_low: assert property (
        @(posedge clk) !B |-> !X
    );

    // A high output requires both inputs to be high.
    check_output_high_requires_both_inputs_high: assert property (
        @(posedge clk) X |-> (A && B)
    );

endmodule