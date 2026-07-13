module logic_function_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1
);

    // Y must equal the implemented NAND-of-ORs logic.
    check_y_boolean_function: assert property (
        @(posedge clk) Y == ~(((A1 | A2) & (B1 | B2) & C1))
    );

    // A low C1 forces the NAND output high.
    check_c1_low_forces_y_high: assert property (
        @(posedge clk) (!C1) |-> (Y == 1'b1)
    );

    // Both A inputs low force the NAND output high.
    check_no_a_input_forces_y_high: assert property (
        @(posedge clk) (!(A1 | A2)) |-> (Y == 1'b1)
    );

    // Both B inputs low force the NAND output high.
    check_no_b_input_forces_y_high: assert property (
        @(posedge clk) (!(B1 | B2)) |-> (Y == 1'b1)
    );

    // When both OR terms and C1 are high, Y must be low.
    check_all_nand_terms_true_forces_y_low: assert property (
        @(posedge clk) (C1 & (A1 | A2) & (B1 | B2)) |-> (Y == 1'b0)
    );

    // A low Y implies both OR terms and C1 are high.
    check_y_low_only_when_all_terms_true: assert property (
        @(posedge clk) (Y == 1'b0) |-> (C1 & (A1 | A2) & (B1 | B2))
    );

endmodule