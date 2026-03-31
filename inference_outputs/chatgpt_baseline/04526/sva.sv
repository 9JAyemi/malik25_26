module my_module_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1
);

    // Y must equal the inverted AND of B1, C1, and the OR of A1/A2.
    check_y_matches_boolean_function: assert property (
        @(posedge clk) Y == ~((A1 | A2) & B1 & C1)
    );

    // If B1 is low, the AND path is blocked and Y must be high.
    check_b1_low_forces_y_high: assert property (
        @(posedge clk) (B1 == 1'b0) |-> (Y == 1'b1)
    );

    // If C1 is low, the AND path is blocked and Y must be high.
    check_c1_low_forces_y_high: assert property (
        @(posedge clk) (C1 == 1'b0) |-> (Y == 1'b1)
    );

    // If both A inputs are low, the OR term is low and Y must be high.
    check_a_inputs_low_force_y_high: assert property (
        @(posedge clk) ((A1 == 1'b0) && (A2 == 1'b0)) |-> (Y == 1'b1)
    );

    // If A1, B1, and C1 are high, the output must be low.
    check_a1_path_drives_y_low: assert property (
        @(posedge clk) ((A1 == 1'b1) && (B1 == 1'b1) && (C1 == 1'b1)) |-> (Y == 1'b0)
    );

    // If A2, B1, and C1 are high, the output must be low.
    check_a2_path_drives_y_low: assert property (
        @(posedge clk) ((A2 == 1'b1) && (B1 == 1'b1) && (C1 == 1'b1)) |-> (Y == 1'b0)
    );

    // A low Y requires the OR term and both AND enables to be high.
    check_y_low_requires_all_terms_high: assert property (
        @(posedge clk) (Y == 1'b0) |-> (((A1 | A2) & B1 & C1) == 1'b1)
    );

endmodule