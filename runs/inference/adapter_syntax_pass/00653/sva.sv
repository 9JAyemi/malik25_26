module and4_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic X
);

    // X must equal the AND of all four inputs.
    check_x_matches_and4: assert property (
        @(posedge clk) X == (A & B & C & D)
    );

    // X must be high when all inputs are high.
    check_x_high_when_all_inputs_high: assert property (
        @(posedge clk) (A & B & C & D) |-> X
    );

    // X must be low when any input is low.
    check_x_low_when_any_input_low: assert property (
        @(posedge clk) (!A || !B || !C || !D) |-> !X
    );

    // A high X requires all inputs to be high.
    check_x_high_requires_all_inputs_high: assert property (
        @(posedge clk) X |-> (A & B & C & D)
    );

endmodule