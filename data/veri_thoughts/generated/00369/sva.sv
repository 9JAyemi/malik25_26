module and_gate_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic A4,
    input logic B1
);

    // Y must equal the AND of all five inputs.
    check_y_matches_and_function: assert property (
        @(posedge clk) Y == (A1 & A2 & A3 & A4 & B1)
    );

    // When all inputs are HIGH, Y must be HIGH.
    check_all_inputs_high_drives_y_high: assert property (
        @(posedge clk) (A1 & A2 & A3 & A4 & B1) |-> Y
    );

    // A HIGH Y requires all inputs to be HIGH.
    check_y_high_requires_all_inputs_high: assert property (
        @(posedge clk) Y |-> (A1 & A2 & A3 & A4 & B1)
    );

    // A LOW A1 forces Y LOW.
    check_a1_low_forces_y_low: assert property (
        @(posedge clk) !A1 |-> !Y
    );

    // A LOW A2 forces Y LOW.
    check_a2_low_forces_y_low: assert property (
        @(posedge clk) !A2 |-> !Y
    );

    // A LOW A3 forces Y LOW.
    check_a3_low_forces_y_low: assert property (
        @(posedge clk) !A3 |-> !Y
    );

    // A LOW A4 forces Y LOW.
    check_a4_low_forces_y_low: assert property (
        @(posedge clk) !A4 |-> !Y
    );

    // A LOW B1 forces Y LOW.
    check_b1_low_forces_y_low: assert property (
        @(posedge clk) !B1 |-> !Y
    );

endmodule