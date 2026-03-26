module sky130_fd_sc_ms__o21ai_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1
);

    // Y implements the inverted AND of B1 with (A1 OR A2).
    check_y_function: assert property (
        @(posedge clk) Y == ~((A1 | A2) & B1)
    );

    // A low B1 forces the NAND output high.
    check_b1_low_forces_y_high: assert property (
        @(posedge clk) (B1 == 1'b0) |-> (Y == 1'b1)
    );

    // When both OR inputs are low, Y must be high.
    check_a_inputs_low_force_y_high: assert property (
        @(posedge clk) ((A1 == 1'b0) && (A2 == 1'b0)) |-> (Y == 1'b1)
    );

    // A1 high with B1 high drives Y low.
    check_a1_and_b1_drive_y_low: assert property (
        @(posedge clk) ((A1 == 1'b1) && (B1 == 1'b1)) |-> (Y == 1'b0)
    );

    // A2 high with B1 high drives Y low.
    check_a2_and_b1_drive_y_low: assert property (
        @(posedge clk) ((A2 == 1'b1) && (B1 == 1'b1)) |-> (Y == 1'b0)
    );

    // A low Y can only occur when B1 is high and at least one A input is high.
    check_y_low_has_valid_cause: assert property (
        @(posedge clk) (Y == 1'b0) |-> ((B1 == 1'b1) && ((A1 == 1'b1) || (A2 == 1'b1)))
    );

endmodule