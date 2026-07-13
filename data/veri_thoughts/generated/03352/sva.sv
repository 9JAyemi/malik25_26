module and4_sva (
    input logic clk,
    input logic Y,
    input logic A,
    input logic B,
    input logic C,
    input logic D
);

    // Y must equal the AND of all four inputs.
    check_y_matches_and4: assert property (
        @(posedge clk) Y == (A & B & C & D)
    );

    // Y high requires all four inputs high.
    check_y_high_requires_all_inputs_high: assert property (
        @(posedge clk) Y |-> (A & B & C & D)
    );

    // All four inputs high must drive Y high.
    check_all_inputs_high_drive_y_high: assert property (
        @(posedge clk) (A & B & C & D) |-> Y
    );

    // Any low input must drive Y low.
    check_any_low_input_drives_y_low: assert property (
        @(posedge clk) (!A || !B || !C || !D) |-> !Y
    );

endmodule