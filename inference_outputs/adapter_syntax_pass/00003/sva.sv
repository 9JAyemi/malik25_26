module sky130_fd_sc_hd__o21bai_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1_N
);

    // Y matches the implemented NOT/OR/NAND/BUF function.
    check_output_function: assert property (
        @(posedge clk) Y == ~((~B1_N) & (A1 | A2))
    );

    // A low B1_N forces Y low.
    check_b1n_low_forces_y_low: assert property (
        @(posedge clk) (B1_N == 1'b0) |-> (Y == 1'b0)
    );

    // A high B1_N forces Y high.
    check_b1n_high_forces_y_high: assert property (
        @(posedge clk) (B1_N == 1'b1) |-> (Y == 1'b1)
    );

    // A1 high with B1_N high forces Y high.
    check_a1_high_with_b1n_high_forces_y_high: assert property (
        @(posedge clk) ((A1 == 1'b1) && (B1_N == 1'b1)) |-> (Y == 1'b1)
    );

    // A2 high with B1_N high forces Y high.
    check_a2_high_with_b1n_high_forces_y_high: assert property (
        @(posedge clk) ((A2 == 1'b1) && (B1_N == 1'b1)) |-> (Y == 1'b1)
    );

    // Both A inputs low with B1_N high force Y low.
    check_a_inputs_low_with_b1n_high_forces_y_low: assert property (
        @(posedge clk) ((A1 == 1'b0) && (A2 == 1'b0) && (B1_N == 1'b1)) |-> (Y == 1'b0)
    );

endmodule