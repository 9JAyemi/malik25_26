module sky130_fd_sc_hdll__and3b_sva (
    input logic clk,
    input logic X,
    input logic A_N,
    input logic B,
    input logic C
);

    // X matches the implemented function ~A_N & B & C.
    check_x_function: assert property (
        @(posedge clk) X == ((~A_N) & B & C)
    );

    // A high X requires all effective AND terms to be high.
    check_x_high_implies_inputs: assert property (
        @(posedge clk) X |-> ((!A_N) && B && C)
    );

    // When all effective AND terms are high, X must be high.
    check_inputs_imply_x_high: assert property (
        @(posedge clk) ((!A_N) && B && C) |-> X
    );

    // A_N high forces X low because A_N is inverted internally.
    check_an_high_forces_x_low: assert property (
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

endmodule