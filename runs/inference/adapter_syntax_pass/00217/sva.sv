module sky130_fd_sc_hd__o221ai_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1
);

    // Y matches the implemented OR-then-NAND function.
    check_y_matches_o221ai_function: assert property (
        @(posedge clk) Y == ~(((A1 | A2) & (B1 | B2)) & C1)
    );

    // C1 low forces the NAND output high.
    check_c1_low_forces_y_high: assert property (
        @(posedge clk) (C1 == 1'b0) |-> (Y == 1'b1)
    );

    // Both A inputs low force the OR term low and Y high.
    check_a_inputs_low_force_y_high: assert property (
        @(posedge clk) ((A1 == 1'b0) && (A2 == 1'b0)) |-> (Y == 1'b1)
    );

    // Both B inputs low force the OR term low and Y high.
    check_b_inputs_low_force_y_high: assert property (
        @(posedge clk) ((B1 == 1'b0) && (B2 == 1'b0)) |-> (Y == 1'b1)
    );

    // With C1 high and both OR terms high, Y must be low.
    check_both_or_terms_high_force_y_low: assert property (
        @(posedge clk) ((C1 == 1'b1) && ((A1 | A2) == 1'b1) && ((B1 | B2) == 1'b1)) |-> (Y == 1'b0)
    );

    // A low Y can only occur when C1 is high and both OR terms are high.
    check_y_low_only_under_active_conditions: assert property (
        @(posedge clk) (Y == 1'b0) |-> ((C1 == 1'b1) && ((A1 | A2) == 1'b1) && ((B1 | B2) == 1'b1))
    );

endmodule