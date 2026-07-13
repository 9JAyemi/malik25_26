module sky130_fd_sc_lp__a21boi_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1_N
);

    // Y matches the implemented NOT/AND/NOR/BUF logic.
    check_y_matches_logic: assert property (
        @(posedge clk) Y == ~((~B1_N) | (A1 & A2))
    );

    // A low B1_N input forces Y low.
    check_b1n_low_forces_y_low: assert property (
        @(posedge clk) (B1_N == 1'b0) |-> (Y == 1'b0)
    );

    // A high Y requires both A inputs to be low.
    check_y_high_requires_a_inputs_low: assert property (
        @(posedge clk) (Y == 1'b1) |-> ((A1 == 1'b0) && (A2 == 1'b0))
    );

    // A high A1 input forces Y low.
    check_a1_high_forces_y_low: assert property (
        @(posedge clk) (A1 == 1'b1) |-> (Y == 1'b0)
    );

    // A high A2 input forces Y low.
    check_a2_high_forces_y_low: assert property (
        @(posedge clk) (A2 == 1'b1) |-> (Y == 1'b0)
    );

    // With both A inputs low, Y follows B1_N.
    check_a_inputs_low_passes_b1n: assert property (
        @(posedge clk) ((A1 == 1'b0) && (A2 == 1'b0)) |-> (Y == B1_N)
    );

endmodule