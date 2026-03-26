module sky130_fd_sc_ms__nand2b_sva (
    input logic clk,
    input logic Y,
    input logic A_N,
    input logic B
);

    // Y matches the implemented logic A_N | ~B.
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

    // A_N low with B high drives Y low.
    check_low_input_combination_drives_y_low: assert property (
        @(posedge clk) (!A_N && B) |-> !Y
    );

    // Y low implies the unique low-output input combination.
    check_y_low_implies_unique_input_case: assert property (
        @(posedge clk) !Y |-> (!A_N && B)
    );

    // If Y is high while A_N is low, then B must be low.
    check_y_high_with_a_n_low_implies_b_low: assert property (
        @(posedge clk) (Y && !A_N) |-> !B
    );

endmodule