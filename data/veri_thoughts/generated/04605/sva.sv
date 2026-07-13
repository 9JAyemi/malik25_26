module sky130_fd_sc_hd__and4bb_sva (
    input logic clk,
    input logic A_N,
    input logic B_N,
    input logic C,
    input logic D,
    input logic X
);

    // X implements (~A_N) & (~B_N) & C & D.
    check_boolean_function: assert property (
        @(posedge clk) X == ((~A_N) & (~B_N) & C & D)
    );

    // X can only be high when all four effective AND terms are high.
    check_x_high_only_when_enabled: assert property (
        @(posedge clk) X |-> (!A_N && !B_N && C && D)
    );

    // X must be high when all four effective AND terms are high.
    check_x_high_when_all_terms_high: assert property (
        @(posedge clk) (!A_N && !B_N && C && D) |-> X
    );

    // A_N high forces X low.
    check_a_n_blocks_output: assert property (
        @(posedge clk) A_N |-> !X
    );

    // B_N high forces X low.
    check_b_n_blocks_output: assert property (
        @(posedge clk) B_N |-> !X
    );

    // C low forces X low.
    check_c_low_blocks_output: assert property (
        @(posedge clk) !C |-> !X
    );

    // D low forces X low.
    check_d_low_blocks_output: assert property (
        @(posedge clk) !D |-> !X
    );

endmodule