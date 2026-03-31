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

    // A low must force X low.
    check_a_low_forces_x_low: assert property (
        @(posedge clk) !A |-> !X
    );

    // B low must force X low.
    check_b_low_forces_x_low: assert property (
        @(posedge clk) !B |-> !X
    );

    // C low must force X low.
    check_c_low_forces_x_low: assert property (
        @(posedge clk) !C |-> !X
    );

    // D low must force X low.
    check_d_low_forces_x_low: assert property (
        @(posedge clk) !D |-> !X
    );

endmodule