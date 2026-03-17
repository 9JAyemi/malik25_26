module sky130_fd_sc_ms__nand4b_sva (
    input logic Y,
    input logic A_N,
    input logic B,
    input logic C,
    input logic D,
    input logic clk
);

    // Sample on an external clock because this cell is combinational and has no reset.

    // Y matches the buffered 4-input NAND with A_N inverted internally.
    check_function_equivalence: assert property (
        @(posedge clk) Y == ~(D & C & B & ~A_N)
    );

    // All effective NAND inputs high drive the output low.
    check_all_active_inputs_drive_low: assert property (
        @(posedge clk) (!A_N && B && C && D) |-> !Y
    );

    // A low output requires the single active-input minterm.
    check_low_output_requires_all_active_inputs: assert property (
        @(posedge clk) !Y |-> (!A_N && B && C && D)
    );

    // A_N high forces the output high.
    check_a_n_high_forces_high: assert property (
        @(posedge clk) A_N |-> Y
    );

    // B low forces the output high.
    check_b_low_forces_high: assert property (
        @(posedge clk) !B |-> Y
    );

    // C low forces the output high.
    check_c_low_forces_high: assert property (
        @(posedge clk) !C |-> Y
    );

    // D low forces the output high.
    check_d_low_forces_high: assert property (
        @(posedge clk) !D |-> Y
    );

    // A high output means at least one input blocks the low minterm.
    check_high_output_has_blocking_input: assert property (
        @(posedge clk) Y |-> (A_N || !B || !C || !D)
    );

endmodule