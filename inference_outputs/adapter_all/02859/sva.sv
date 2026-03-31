module and4bb_sva (
    input logic clk,
    input logic A_N,
    input logic B_N,
    input logic C,
    input logic D,
    input logic X
);

    // X must equal the AND of all four inputs.
    check_x_matches_and: assert property (
        @(posedge clk) X == (A_N & B_N & C & D)
    );

    // All inputs high must drive X high.
    check_all_inputs_high_drive_x_high: assert property (
        @(posedge clk) (A_N && B_N && C && D) |-> X
    );

    // A_N low must force X low.
    check_a_n_low_forces_x_low: assert property (
        @(posedge clk) !A_N |-> !X
    );

    // B_N low must force X low.
    check_b_n_low_forces_x_low: assert property (
        @(posedge clk) !B_N |-> !X
    );

    // C low must force X low.
    check_c_low_forces_x_low: assert property (
        @(posedge clk) !C |-> !X
    );

    // D low must force X low.
    check_d_low_forces_x_low: assert property (
        @(posedge clk) !D |-> !X
    );

    // X high requires all inputs high.
    check_x_high_requires_all_inputs_high: assert property (
        @(posedge clk) X |-> (A_N && B_N && C && D)
    );

endmodule