module sky130_fd_sc_hs__nand4bb_sva (
    input logic clk,
    input logic Y,
    input logic A_N,
    input logic B_N,
    input logic C,
    input logic D
);

    // Y matches the RTL NAND equation.
    check_nand_function: assert property (
        @(posedge clk) Y == ~(A_N & B_N & C & D)
    );

    // All four inputs high drives Y low.
    check_all_high_drives_low: assert property (
        @(posedge clk) (A_N & B_N & C & D) |-> !Y
    );

    // A_N low forces Y high.
    check_a_low_drives_high: assert property (
        @(posedge clk) !A_N |-> Y
    );

    // B_N low forces Y high.
    check_b_low_drives_high: assert property (
        @(posedge clk) !B_N |-> Y
    );

    // C low forces Y high.
    check_c_low_drives_high: assert property (
        @(posedge clk) !C |-> Y
    );

    // D low forces Y high.
    check_d_low_drives_high: assert property (
        @(posedge clk) !D |-> Y
    );

    // Y low can only occur when all inputs are high.
    check_low_output_requires_all_high: assert property (
        @(posedge clk) !Y |-> (A_N & B_N & C & D)
    );

    // Y high implies at least one input is low.
    check_high_output_requires_some_low_input: assert property (
        @(posedge clk) Y |-> (!A_N || !B_N || !C || !D)
    );

endmodule