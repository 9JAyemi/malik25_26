module sky130_fd_sc_ms__a21boi_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1_N
);

    // Y must match the implemented NOT/AND/NOR/BUF logic.
    check_y_matches_implemented_logic: assert property (
        @(posedge clk) (Y == (~((~B1_N) | (A1 & A2))))
    );

    // A low B1_N forces the NOR output, and therefore Y, low.
    check_b1n_low_forces_y_low: assert property (
        @(posedge clk) (B1_N == 1'b0) |-> (Y == 1'b0)
    );

    // High A1 and A2 drive the AND term high and force Y low.
    check_a1_a2_high_force_y_low: assert property (
        @(posedge clk) ((A1 == 1'b1) && (A2 == 1'b1)) |-> (Y == 1'b0)
    );

    // With B1_N high and A1 low, the NOR output must be high.
    check_b1n_high_a1_low_drives_y_high: assert property (
        @(posedge clk) ((B1_N == 1'b1) && (A1 == 1'b0)) |-> (Y == 1'b1)
    );

    // With B1_N high and A2 low, the NOR output must be high.
    check_b1n_high_a2_low_drives_y_high: assert property (
        @(posedge clk) ((B1_N == 1'b1) && (A2 == 1'b0)) |-> (Y == 1'b1)
    );

endmodule