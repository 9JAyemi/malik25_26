module sky130_fd_sc_ms__o211ai_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1
);

    // Y matches the implemented OR-then-NAND function.
    check_y_matches_o211ai_function: assert property (
        @(posedge clk) Y == ~((A1 | A2) & B1 & C1)
    );

    // A low B1 input forces Y high.
    check_b1_low_forces_y_high: assert property (
        @(posedge clk) (B1 == 1'b0) |-> (Y == 1'b1)
    );

    // A low C1 input forces Y high.
    check_c1_low_forces_y_high: assert property (
        @(posedge clk) (C1 == 1'b0) |-> (Y == 1'b1)
    );

    // Both A inputs low force Y high.
    check_a_inputs_low_force_y_high: assert property (
        @(posedge clk) ((A1 == 1'b0) && (A2 == 1'b0)) |-> (Y == 1'b1)
    );

    // With B1 and C1 high, Y is the inverse of A1 OR A2.
    check_y_is_inverted_or_when_b1_c1_high: assert property (
        @(posedge clk) ((B1 == 1'b1) && (C1 == 1'b1)) |-> (Y == ~(A1 | A2))
    );

    // A high Y means the OR term is low and C1 is high.
    check_y_high_implies_or_term_low_and_c1_high: assert property (
        @(posedge clk) (Y == 1'b1) |-> (((A1 | A2) == 1'b0) && (C1 == 1'b1))
    );

    // A low Y means the OR term is high or C1 is low.
    check_y_low_implies_or_term_high_or_c1_low: assert property (
        @(posedge clk) (Y == 1'b0) |-> (((A1 | A2) == 1'b1) || (C1 == 1'b0))
    );

endmodule