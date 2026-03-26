module sky130_fd_sc_lp__and4bb_assertions (
    input logic X,
    input logic A_N,
    input logic B_N,
    input logic C,
    input logic D,
    input logic clk
);

    // X must match the NOR(A_N,B_N) then AND with C and D.
    check_function_equivalence: assert property (
        @(posedge clk) (X == ((~(A_N | B_N)) & C & D))
    );

    // A_N high forces the output low.
    check_a_n_blocks_output: assert property (
        @(posedge clk) (A_N == 1'b1) |-> (X == 1'b0)
    );

    // B_N high forces the output low.
    check_b_n_blocks_output: assert property (
        @(posedge clk) (B_N == 1'b1) |-> (X == 1'b0)
    );

    // C low forces the output low.
    check_c_low_blocks_output: assert property (
        @(posedge clk) (C == 1'b0) |-> (X == 1'b0)
    );

    // D low forces the output low.
    check_d_low_blocks_output: assert property (
        @(posedge clk) (D == 1'b0) |-> (X == 1'b0)
    );

    // The single enabling input combination drives X high.
    check_enabling_combination_sets_output: assert property (
        @(posedge clk) ((A_N == 1'b0) && (B_N == 1'b0) && (C == 1'b1) && (D == 1'b1)) |-> (X == 1'b1)
    );

    // A high output implies both inverted inputs are low and C/D are high.
    check_output_high_implies_inputs: assert property (
        @(posedge clk) (X == 1'b1) |-> ((A_N == 1'b0) && (B_N == 1'b0) && (C == 1'b1) && (D == 1'b1))
    );

endmodule