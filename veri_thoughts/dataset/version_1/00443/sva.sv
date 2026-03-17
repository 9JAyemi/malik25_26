module sky130_fd_sc_ls__o21a_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1
);

    // X must equal the OR of A1/A2 gated by B1.
    check_output_function: assert property (
        @(posedge clk) X === ((A1 | A2) & B1)
    );

    // B1 low forces X low.
    check_b1_low_blocks_output: assert property (
        @(posedge clk) (B1 === 1'b0) |-> (X === 1'b0)
    );

    // Both A inputs low force X low.
    check_a_inputs_low_blocks_output: assert property (
        @(posedge clk) ((A1 === 1'b0) && (A2 === 1'b0)) |-> (X === 1'b0)
    );

    // A1 high with B1 high drives X high.
    check_a1_with_b1_drives_output: assert property (
        @(posedge clk) ((A1 === 1'b1) && (B1 === 1'b1)) |-> (X === 1'b1)
    );

    // A2 high with B1 high drives X high.
    check_a2_with_b1_drives_output: assert property (
        @(posedge clk) ((A2 === 1'b1) && (B1 === 1'b1)) |-> (X === 1'b1)
    );

    // X high requires B1 high.
    check_output_requires_b1: assert property (
        @(posedge clk) (X === 1'b1) |-> (B1 === 1'b1)
    );

    // X high requires at least one A input high.
    check_output_requires_a_input: assert property (
        @(posedge clk) (X === 1'b1) |-> ((A1 === 1'b1) || (A2 === 1'b1))
    );

endmodule