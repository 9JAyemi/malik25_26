module my_module_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1
);

    // Y matches the implemented OR/AND/NOT function.
    check_y_matches_function: assert property (
        @(posedge clk) Y == ~((A1 | A2) & B1 & C1)
    );

    // A low B1 forces the output high.
    check_b1_low_forces_y_high: assert property (
        @(posedge clk) (B1 == 1'b0) |-> (Y == 1'b1)
    );

    // A low C1 forces the output high.
    check_c1_low_forces_y_high: assert property (
        @(posedge clk) (C1 == 1'b0) |-> (Y == 1'b1)
    );

    // Both A inputs low force the output high.
    check_a_inputs_low_force_y_high: assert property (
        @(posedge clk) ((A1 == 1'b0) && (A2 == 1'b0)) |-> (Y == 1'b1)
    );

    // With B1 and C1 high, A1 high forces the output low.
    check_a1_high_with_b1_c1_high_forces_y_low: assert property (
        @(posedge clk) ((B1 == 1'b1) && (C1 == 1'b1) && (A1 == 1'b1)) |-> (Y == 1'b0)
    );

    // With B1 and C1 high, A2 high forces the output low.
    check_a2_high_with_b1_c1_high_forces_y_low: assert property (
        @(posedge clk) ((B1 == 1'b1) && (C1 == 1'b1) && (A2 == 1'b1)) |-> (Y == 1'b0)
    );

    // A low output requires B1 and C1 high and at least one A input high.
    check_y_low_requires_active_inputs: assert property (
        @(posedge clk) (Y == 1'b0) |-> ((B1 == 1'b1) && (C1 == 1'b1) && ((A1 == 1'b1) || (A2 == 1'b1)))
    );

endmodule