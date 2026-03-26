module sky130_fd_sc_ls__nand4_sva (
    input logic clk,
    input logic Y,
    input logic A,
    input logic B,
    input logic C,
    input logic D
);

    // Y must match the 4-input NAND of A, B, C, and D.
    check_nand_function: assert property (
        @(posedge clk) Y === ~(A & B & C & D)
    );

    // All inputs high must drive Y low.
    check_all_inputs_high_drives_low: assert property (
        @(posedge clk)
        (A === 1'b1 && B === 1'b1 && C === 1'b1 && D === 1'b1) |-> (Y === 1'b0)
    );

    // A low must force Y high.
    check_a_low_forces_high: assert property (
        @(posedge clk) (A === 1'b0) |-> (Y === 1'b1)
    );

    // B low must force Y high.
    check_b_low_forces_high: assert property (
        @(posedge clk) (B === 1'b0) |-> (Y === 1'b1)
    );

    // C low must force Y high.
    check_c_low_forces_high: assert property (
        @(posedge clk) (C === 1'b0) |-> (Y === 1'b1)
    );

    // D low must force Y high.
    check_d_low_forces_high: assert property (
        @(posedge clk) (D === 1'b0) |-> (Y === 1'b1)
    );

    // A low output requires all inputs to be high.
    check_low_output_requires_all_inputs_high: assert property (
        @(posedge clk)
        (Y === 1'b0) |-> (A === 1'b1 && B === 1'b1 && C === 1'b1 && D === 1'b1)
    );

    // If sampled inputs do not change, sampled output must not change.
    check_stable_inputs_keep_stable_output: assert property (
        @(posedge clk) $stable({A, B, C, D}) |-> $stable(Y)
    );

endmodule