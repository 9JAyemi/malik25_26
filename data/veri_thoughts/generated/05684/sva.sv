module sky130_fd_sc_hd__nor3b_sva (
    input logic clk,
    input logic Y,
    input logic A,
    input logic B,
    input logic C_N
);

    // Y matches the implemented NOR-AND-buffer function.
    check_output_function: assert property (
        @(posedge clk) Y === (C_N & (~A) & (~B))
    );

    // A high forces the output low.
    check_a_high_forces_low: assert property (
        @(posedge clk) (A === 1'b1) |-> (Y === 1'b0)
    );

    // B high forces the output low.
    check_b_high_forces_low: assert property (
        @(posedge clk) (B === 1'b1) |-> (Y === 1'b0)
    );

    // C_N low blocks the output.
    check_cn_low_forces_low: assert property (
        @(posedge clk) (C_N === 1'b0) |-> (Y === 1'b0)
    );

    // With A and B low, Y follows C_N.
    check_ab_low_y_follows_cn: assert property (
        @(posedge clk) ((A === 1'b0) && (B === 1'b0)) |-> (Y === C_N)
    );

    // A high output requires both inputs low and C_N high.
    check_y_high_requires_inputs: assert property (
        @(posedge clk) (Y === 1'b1) |-> ((A === 1'b0) && (B === 1'b0) && (C_N === 1'b1))
    );

endmodule