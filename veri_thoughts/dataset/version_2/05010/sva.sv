module sky130_fd_sc_lp__and4_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic B,
    input logic C,
    input logic D
);

    // X equals the AND of A, B, C, and D.
    check_x_matches_and4: assert property (
        @(posedge clk) X == (A & B & C & D)
    );

    // All inputs high drives X high.
    check_all_high_drives_x_high: assert property (
        @(posedge clk) (A && B && C && D) |-> X
    );

    // Any low input drives X low.
    check_any_low_drives_x_low: assert property (
        @(posedge clk) (!A || !B || !C || !D) |-> !X
    );

    // X high requires all inputs high.
    check_x_high_requires_all_high: assert property (
        @(posedge clk) X |-> (A && B && C && D)
    );

    // X low requires at least one input low.
    check_x_low_requires_some_input_low: assert property (
        @(posedge clk) !X |-> (!A || !B || !C || !D)
    );

endmodule