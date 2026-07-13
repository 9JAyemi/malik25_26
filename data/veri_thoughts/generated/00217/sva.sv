module sky130_fd_sc_hd__o221ai_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1
);

    // Y must match the implemented O221AI logic function.
    check_y_matches_o221ai_function: assert property (
        @(posedge clk) disable iff (1'b0)
        Y == ~(((A1 | A2) & (B1 | B2) & C1))
    );

    // A low C1 forces the NAND output high.
    check_y_high_when_c1_low: assert property (
        @(posedge clk) disable iff (1'b0)
        (C1 == 1'b0) |-> (Y == 1'b1)
    );

    // Both A inputs low force the A-side OR term low and Y high.
    check_y_high_when_a_group_low: assert property (
        @(posedge clk) disable iff (1'b0)
        ((A1 == 1'b0) && (A2 == 1'b0)) |-> (Y == 1'b1)
    );

    // Both B inputs low force the B-side OR term low and Y high.
    check_y_high_when_b_group_low: assert property (
        @(posedge clk) disable iff (1'b0)
        ((B1 == 1'b0) && (B2 == 1'b0)) |-> (Y == 1'b1)
    );

    // All three NAND inputs high force Y low.
    check_y_low_when_all_nand_inputs_high: assert property (
        @(posedge clk) disable iff (1'b0)
        (((A1 | A2) == 1'b1) && ((B1 | B2) == 1'b1) && (C1 == 1'b1)) |-> (Y == 1'b0)
    );

    // A low Y requires both OR terms and C1 to be high.
    check_y_low_requires_all_nand_inputs_high: assert property (
        @(posedge clk) disable iff (1'b0)
        (Y == 1'b0) |-> (((A1 | A2) == 1'b1) && ((B1 | B2) == 1'b1) && (C1 == 1'b1))
    );

    // With C1 and the B-side OR term high, Y is the inverse of the A-side OR term.
    check_y_reflects_a_group_when_c1_and_b_group_high: assert property (
        @(posedge clk) disable iff (1'b0)
        ((C1 == 1'b1) && ((B1 | B2) == 1'b1)) |-> (Y == ~(A1 | A2))
    );

    // With C1 and the A-side OR term high, Y is the inverse of the B-side OR term.
    check_y_reflects_b_group_when_c1_and_a_group_high: assert property (
        @(posedge clk) disable iff (1'b0)
        ((C1 == 1'b1) && ((A1 | A2) == 1'b1)) |-> (Y == ~(B1 | B2))
    );

    // With both OR terms high, Y is the inverse of C1.
    check_y_reflects_c1_when_both_or_terms_high: assert property (
        @(posedge clk) disable iff (1'b0)
        (((A1 | A2) == 1'b1) && ((B1 | B2) == 1'b1)) |-> (Y == ~C1)
    );

endmodule