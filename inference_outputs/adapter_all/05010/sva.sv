module sky130_fd_sc_lp__and4_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic B,
    input logic C,
    input logic D
);

    // X must equal the AND of all four inputs.
    check_and_function: assert property (
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

    // Any low input must force X low.
    check_any_input_low_forces_x_low: assert property (
        @(posedge clk) !(A & B & C & D) |-> !X
    );

    // With B, C, and D high, X must follow A.
    check_x_follows_a_when_others_high: assert property (
        @(posedge clk) (B & C & D) |-> (X == A)
    );

    // With A, C, and D high, X must follow B.
    check_x_follows_b_when_others_high: assert property (
        @(posedge clk) (A & C & D) |-> (X == B)
    );

    // With A, B, and D high, X must follow C.
    check_x_follows_c_when_others_high: assert property (
        @(posedge clk) (A & B & D) |-> (X == C)
    );

    // With A, B, and C high, X must follow D.
    check_x_follows_d_when_others_high: assert property (
        @(posedge clk) (A & B & C) |-> (X == D)
    );

endmodule