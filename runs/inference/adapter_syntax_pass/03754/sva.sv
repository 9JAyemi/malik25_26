module sky130_fd_sc_ms__nand2b_sva (
    input logic clk,
    input logic Y,
    input logic A_N,
    input logic B
);

    // Y matches the implemented NOT-OR function.
    check_output_function: assert property (
        @(posedge clk) Y == (A_N | ~B)
    );

    // A_N high forces Y high.
    check_a_n_high_forces_y_high: assert property (
        @(posedge clk) A_N |-> Y
    );

    // B low forces Y high.
    check_b_low_forces_y_high: assert property (
        @(posedge clk) !B |-> Y
    );

    // A_N low with B high forces Y low.
    check_low_input_combination_forces_y_low: assert property (
        @(posedge clk) (!A_N && B) |-> !Y
    );

    // Y low implies the low-input combination is active.
    check_y_low_implies_low_input_combination: assert property (
        @(posedge clk) !Y |-> (!A_N && B)
    );

endmodule