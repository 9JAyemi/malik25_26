module sky130_fd_sc_ls__and3b_sva (
    input logic clk,
    input logic X,
    input logic A_N,
    input logic B,
    input logic C
);

    // Sampling clock for this combinational cell; the RTL has no reset.

    // X implements the function (~A_N) & B & C.
    check_and3b_function: assert property (
        @(posedge clk) X == ((~A_N) & B & C)
    );

    // A_N high forces X low.
    check_a_n_high_forces_x_low: assert property (
        @(posedge clk) A_N |-> !X
    );

    // B low forces X low.
    check_b_low_forces_x_low: assert property (
        @(posedge clk) !B |-> !X
    );

    // C low forces X low.
    check_c_low_forces_x_low: assert property (
        @(posedge clk) !C |-> !X
    );

    // A_N low with B and C high drives X high.
    check_all_inputs_drive_x_high: assert property (
        @(posedge clk) (!A_N && B && C) |-> X
    );

    // X high requires A_N low and both B and C high.
    check_x_high_requires_inputs: assert property (
        @(posedge clk) X |-> (!A_N && B && C)
    );

endmodule