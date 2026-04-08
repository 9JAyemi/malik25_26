module sky130_fd_sc_lp__o221ai_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1
);

    // Y implements the buffered NAND of (A1|A2), (B1|B2), and C1.
    check_o221ai_equation: assert property (
        @(posedge clk)
        Y == ~(((A1 | A2) & (B1 | B2) & C1))
    );

    // A low C1 input forces the NAND output high.
    check_c1_low_forces_y_high: assert property (
        @(posedge clk)
        (C1 == 1'b0) |-> (Y == 1'b1)
    );

    // Both A inputs low force the first OR term low and Y high.
    check_a_inputs_low_force_y_high: assert property (
        @(posedge clk)
        ((A1 == 1'b0) && (A2 == 1'b0)) |-> (Y == 1'b1)
    );

    // Both B inputs low force the second OR term low and Y high.
    check_b_inputs_low_force_y_high: assert property (
        @(posedge clk)
        ((B1 == 1'b0) && (B2 == 1'b0)) |-> (Y == 1'b1)
    );

    // When both OR terms and C1 are high, the NAND output must be low.
    check_all_terms_high_drive_y_low: assert property (
        @(posedge clk)
        (((A1 | A2) == 1'b1) && ((B1 | B2) == 1'b1) && (C1 == 1'b1)) |-> (Y == 1'b0)
    );

    // A low Y can only occur when both OR terms and C1 are high.
    check_y_low_requires_all_terms_high: assert property (
        @(posedge clk)
        (Y == 1'b0) |-> (((A1 | A2) == 1'b1) && ((B1 | B2) == 1'b1) && (C1 == 1'b1))
    );

endmodule