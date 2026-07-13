module custom_module_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1
);

    // X must equal the AND of A1, A2, and B1.
    check_x_matches_and_function: assert property (
        @(posedge clk) X == (A1 & A2 & B1)
    );

    // A low B1 forces X low.
    check_b1_low_forces_x_low: assert property (
        @(posedge clk) !B1 |-> !X
    );

    // A low A1 forces X low.
    check_a1_low_forces_x_low: assert property (
        @(posedge clk) !A1 |-> !X
    );

    // A low A2 forces X low.
    check_a2_low_forces_x_low: assert property (
        @(posedge clk) !A2 |-> !X
    );

    // All three high inputs drive X high.
    check_all_inputs_high_drive_x_high: assert property (
        @(posedge clk) (A1 & A2 & B1) |-> X
    );

    // A high X requires all three inputs to be high.
    check_x_high_requires_all_inputs_high: assert property (
        @(posedge clk) X |-> (A1 & A2 & B1)
    );

endmodule