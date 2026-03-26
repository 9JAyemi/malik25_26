module sky130_fd_sc_ms__or4bb_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic B,
    input logic C_N,
    input logic D_N
);

    // X matches the implemented OR/NAND/BUF boolean function.
    check_boolean_function: assert property (
        @(posedge clk) X == (A | B | ~(C_N & D_N))
    );

    // A high forces X high.
    check_a_high_sets_output: assert property (
        @(posedge clk) A |-> X
    );

    // B high forces X high.
    check_b_high_sets_output: assert property (
        @(posedge clk) B |-> X
    );

    // Low C_N forces X high through the NAND term.
    check_c_n_low_sets_output: assert property (
        @(posedge clk) !C_N |-> X
    );

    // Low D_N forces X high through the NAND term.
    check_d_n_low_sets_output: assert property (
        @(posedge clk) !D_N |-> X
    );

    // X low requires all OR inputs to be inactive.
    check_output_low_requires_all_inactive: assert property (
        @(posedge clk) !X |-> (!A && !B && C_N && D_N)
    );

    // All inactive OR inputs produce a low X.
    check_all_inactive_gives_low: assert property (
        @(posedge clk) (!A && !B && C_N && D_N) |-> !X
    );

endmodule