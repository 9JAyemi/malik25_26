module sky130_fd_sc_hd__and3b_sva (
    input logic clk,
    input logic X,
    input logic A_N,
    input logic B,
    input logic C
);

    // X implements the combinational function (~A_N & B & C).
    check_functional_equivalence: assert property (
        @(posedge clk) X === ((~A_N) & B & C)
    );

    // A_N high forces the inverted input low and drives X low.
    check_a_n_high_blocks_output: assert property (
        @(posedge clk) (A_N === 1'b1) |-> (X === 1'b0)
    );

    // B low forces the 3-input AND output low.
    check_b_low_blocks_output: assert property (
        @(posedge clk) (B === 1'b0) |-> (X === 1'b0)
    );

    // C low forces the 3-input AND output low.
    check_c_low_blocks_output: assert property (
        @(posedge clk) (C === 1'b0) |-> (X === 1'b0)
    );

    // When all effective AND inputs are high, X must be high.
    check_all_inputs_enable_output_high: assert property (
        @(posedge clk) (A_N === 1'b0 && B === 1'b1 && C === 1'b1) |-> (X === 1'b1)
    );

    // X high is only possible for the single true minterm.
    check_output_high_implies_required_inputs: assert property (
        @(posedge clk) (X === 1'b1) |-> (A_N === 1'b0 && B === 1'b1 && C === 1'b1)
    );

endmodule