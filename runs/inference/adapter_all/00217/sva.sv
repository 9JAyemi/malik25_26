module sky130_fd_sc_hd__o221ai_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1
);

    // Y matches the implemented OR-OR-NAND function.
    check_function_equivalence: assert property (
        @(posedge clk) Y == ~((A1 | A2) & (B1 | B2) & C1)
    );

    // C1 low forces the NAND output high.
    check_c1_low_forces_y_high: assert property (
        @(posedge clk) !C1 |-> Y
    );

    // Both A inputs low force the NAND output high.
    check_a_inputs_low_force_y_high: assert property (
        @(posedge clk) !(A1 | A2) |-> Y
    );

    // Both B inputs low force the NAND output high.
    check_b_inputs_low_force_y_high: assert property (
        @(posedge clk) !(B1 | B2) |-> Y
    );

    // All three active terms force the NAND output low.
    check_all_terms_active_force_y_low: assert property (
        @(posedge clk) (C1 && (A1 | A2) && (B1 | B2)) |-> !Y
    );

    // A low Y requires C1 and at least one A and one B term.
    check_y_low_requires_all_terms_active: assert property (
        @(posedge clk) !Y |-> (C1 && (A1 | A2) && (B1 | B2))
    );

    // With C1 high, a low Y requires both A terms high.
    check_c1_high_y_low_requires_a_terms: assert property (
        @(posedge clk) (C1 && !Y) |-> (A1 && A2)
    );

    // With C1 high, a low Y requires both B terms high.
    check_c1_high_y_low_requires_b_terms: assert property (
        @(posedge clk) (C1 && !Y) |-> (B1 && B2)
    );

endmodule