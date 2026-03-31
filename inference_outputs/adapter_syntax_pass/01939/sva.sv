module my_module_sva (
    input logic clk,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic X
);

    // X must equal the implemented AND/NOT function.
    check_x_matches_function: assert property (
        @(posedge clk) X == ((A1 & A2) & ~(B1 & B2))
    );

    // A low A1 input forces X low.
    check_a1_low_forces_x_low: assert property (
        @(posedge clk) !A1 |-> !X
    );

    // A low A2 input forces X low.
    check_a2_low_forces_x_low: assert property (
        @(posedge clk) !A2 |-> !X
    );

    // A high B1 input forces X low.
    check_b1_high_forces_x_low: assert property (
        @(posedge clk) B1 |-> !X
    );

    // A high B2 input forces X low.
    check_b2_high_forces_x_low: assert property (
        @(posedge clk) B2 |-> !X
    );

    // A high X requires both A inputs high.
    check_x_high_requires_a_inputs: assert property (
        @(posedge clk) X |-> (A1 & A2)
    );

    // A high X requires both B inputs low.
    check_x_high_requires_b_inputs_low: assert property (
        @(posedge clk) X |-> !(B1 & B2)
    );

    // With both A inputs high and both B inputs low, X must be high.
    check_all_terms_true_sets_x_high: assert property (
        @(posedge clk) (A1 & A2 & !B1 & !B2) |-> X
    );

endmodule