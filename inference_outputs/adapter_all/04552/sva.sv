module logic_function_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1
);

    // Y matches the implemented OR-OR-NAND function.
    check_y_matches_logic_function: assert property (
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

    // A low Y requires all three active terms to be present.
    check_y_low_requires_all_terms_active: assert property (
        @(posedge clk) !Y |-> (C1 && (A1 | A2) && (B1 | B2))
    );

    // With C1 and both A inputs high, Y reduces to the inverted OR of B inputs.
    check_c1_and_a_high_reduces_to_not_b_or: assert property (
        @(posedge clk) (C1 && A1 && A2) |-> (Y == ~(B1 | B2))
    );

    // With C1 and both B inputs high, Y reduces to the inverted OR of A inputs.
    check_c1_and_b_high_reduces_to_not_a_or: assert property (
        @(posedge clk) (C1 && B1 && B2) |-> (Y == ~(A1 | A2))
    );

    // With C1 low and both A inputs high, Y is the OR of the B inputs.
    check_c1_low_and_a_high_reduces_to_b_or: assert property (
        @(posedge clk) (!C1 && A1 && A2) |-> (Y == (B1 | B2))
    );

    // With C1 low and both B inputs high, Y is the OR of the A inputs.
    check_c1_low_and_b_high_reduces_to_a_or: assert property (
        @(posedge clk) (!C1 && B1 && B2) |-> (Y == (A1 | A2))
    );

endmodule