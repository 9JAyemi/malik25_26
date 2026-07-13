module sky130_fd_sc_ls__or4b_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic B,
    input logic C,
    input logic D_N
);

    // X matches the implemented OR-of-A/B/C and inverted D_N.
    check_functional_equivalence: assert property (
        @(posedge clk) X == (A | B | C | ~D_N)
    );

    // A high forces X high.
    check_a_high_sets_x: assert property (
        @(posedge clk) A |-> X
    );

    // B high forces X high.
    check_b_high_sets_x: assert property (
        @(posedge clk) B |-> X
    );

    // C high forces X high.
    check_c_high_sets_x: assert property (
        @(posedge clk) C |-> X
    );

    // D_N low forces X high.
    check_d_n_low_sets_x: assert property (
        @(posedge clk) !D_N |-> X
    );

    // All OR inputs low force X low.
    check_all_inputs_low_clear_x: assert property (
        @(posedge clk) (!A && !B && !C && D_N) |-> !X
    );

    // X low requires all OR inputs to be inactive.
    check_x_low_requires_all_inputs_inactive: assert property (
        @(posedge clk) !X |-> (!A && !B && !C && D_N)
    );

endmodule