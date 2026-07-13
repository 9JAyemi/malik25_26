module and4_module_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic B,
    input logic C,
    input logic D
);

    // X must equal the AND of all four inputs.
    check_output_matches_and: assert property (
        @(posedge clk) X == (A & B & C & D)
    );

    // All HIGH inputs must drive X HIGH.
    check_all_inputs_high_drive_x_high: assert property (
        @(posedge clk) (A && B && C && D) |-> (X == 1'b1)
    );

    // A LOW input must drive X LOW.
    check_a_low_forces_x_low: assert property (
        @(posedge clk) (!A) |-> (X == 1'b0)
    );

    // B LOW input must drive X LOW.
    check_b_low_forces_x_low: assert property (
        @(posedge clk) (!B) |-> (X == 1'b0)
    );

    // C LOW input must drive X LOW.
    check_c_low_forces_x_low: assert property (
        @(posedge clk) (!C) |-> (X == 1'b0)
    );

    // D LOW input must drive X LOW.
    check_d_low_forces_x_low: assert property (
        @(posedge clk) (!D) |-> (X == 1'b0)
    );

    // X HIGH requires all inputs HIGH.
    check_x_high_requires_all_inputs_high: assert property (
        @(posedge clk) X |-> (A && B && C && D)
    );

    // Stable inputs must keep X stable.
    check_stable_inputs_keep_x_stable: assert property (
        @(posedge clk) $stable({A, B, C, D}) |-> $stable(X)
    );

endmodule