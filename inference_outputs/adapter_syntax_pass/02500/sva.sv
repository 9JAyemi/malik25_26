module sky130_fd_sc_hdll__nand4bb_sva (
    input logic clk,
    input logic Y,
    input logic A_N,
    input logic B_N,
    input logic C,
    input logic D
);

    // Y matches the implemented OR-of-three function.
    check_output_function: assert property (
        @(posedge clk) Y == (A_N | B_N | ~(C & D))
    );

    // A_N high forces Y high.
    check_a_n_forces_high: assert property (
        @(posedge clk) A_N |-> Y
    );

    // B_N high forces Y high.
    check_b_n_forces_high: assert property (
        @(posedge clk) B_N |-> Y
    );

    // C low forces Y high.
    check_c_low_forces_high: assert property (
        @(posedge clk) !C |-> Y
    );

    // D low forces Y high.
    check_d_low_forces_high: assert property (
        @(posedge clk) !D |-> Y
    );

    // A_N and B_N low with C and D high force Y low.
    check_all_terms_low_forces_low: assert property (
        @(posedge clk) (!A_N && !B_N && C && D) |-> !Y
    );

    // Y low implies the A_N/B_N low and C/D high condition.
    check_low_output_condition: assert property (
        @(posedge clk) !Y |-> (!A_N && !B_N && C && D)
    );

endmodule