module four_input_and_sva (
    input logic clk,
    input logic A1,
    input logic A2,
    input logic B1_N,
    input logic C1,
    input logic X
);

    // X matches the implemented combined logic.
    check_output_equation: assert property (
        @(posedge clk) X == (A1 & A2 & ~B1_N & ~C1)
    );

    // When all required terms are enabled, X is high.
    check_enable_combination_sets_x: assert property (
        @(posedge clk) (A1 & A2 & ~B1_N & ~C1) |-> X
    );

    // A high X requires all enabling conditions.
    check_x_high_requires_all_enables: assert property (
        @(posedge clk) X |-> (A1 & A2 & ~B1_N & ~C1)
    );

    // A low A1 forces X low.
    check_a1_low_forces_x_low: assert property (
        @(posedge clk) !A1 |-> !X
    );

    // A low A2 forces X low.
    check_a2_low_forces_x_low: assert property (
        @(posedge clk) !A2 |-> !X
    );

    // A high B1_N forces X low.
    check_b1_n_high_forces_x_low: assert property (
        @(posedge clk) B1_N |-> !X
    );

    // A high C1 forces X low.
    check_c1_high_forces_x_low: assert property (
        @(posedge clk) C1 |-> !X
    );

endmodule