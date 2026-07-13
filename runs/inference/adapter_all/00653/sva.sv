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

    // All inputs high must drive X high.
    check_all_inputs_high_drive_x_high: assert property (
        @(posedge clk) (A & B & C & D) |-> X
    );

    // X high requires all inputs high.
    check_x_high_requires_all_inputs_high: assert property (
        @(posedge clk) X |-> (A & B & C & D)
    );

    // A low forces X low.
    check_a_low_forces_x_low: assert property (
        @(posedge clk) !A |-> !X
    );

    // B low forces X low.
    check_b_low_forces_x_low: assert property (
        @(posedge clk) !B |-> !X
    );

    // C low forces X low.
    check_c_low_forces_x_low: assert property (
        @(posedge clk) !C |-> !X
    );

    // D low forces X low.
    check_d_low_forces_x_low: assert property (
        @(posedge clk) !D |-> !X
    );

    // X can only change when at least one input changes.
    check_x_change_requires_input_change: assert property (
        @(posedge clk) $changed(X) |-> ($changed(A) || $changed(B) || $changed(C) || $changed(D))
    );

    // If all inputs are stable, X must be stable.
    check_stable_inputs_keep_x_stable: assert property (
        @(posedge clk) $stable(A) && $stable(B) && $stable(C) && $stable(D) |-> $stable(X)
    );

endmodule