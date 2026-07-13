module logic_circuit_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1
);

    // Y must match the implemented NOR/AND boolean function.
    check_y_matches_boolean_function: assert property (
        @(posedge clk) Y == ~((B1 & B2) | C1 | (A1 & A2))
    );

    // C1 high forces the NOR output low.
    check_c1_forces_y_low: assert property (
        @(posedge clk) C1 |-> !Y
    );

    // A1 and A2 high together force the NOR output low.
    check_a_pair_forces_y_low: assert property (
        @(posedge clk) (A1 & A2) |-> !Y
    );

    // B1 and B2 high together force the NOR output low.
    check_b_pair_forces_y_low: assert property (
        @(posedge clk) (B1 & B2) |-> !Y
    );

    // A single asserted A input is not enough to pull Y low when other terms are clear.
    check_single_a_input_keeps_y_high: assert property (
        @(posedge clk) (!C1 && !(B1 & B2) && (A1 ^ A2)) |-> Y
    );

    // A single asserted B input is not enough to pull Y low when other terms are clear.
    check_single_b_input_keeps_y_high: assert property (
        @(posedge clk) (!C1 && !(A1 & A2) && (B1 ^ B2)) |-> Y
    );

    // With all NOR inputs low, Y must be high.
    check_all_nor_inputs_low_gives_y_high: assert property (
        @(posedge clk) (!C1 && !(A1 & A2) && !(B1 & B2)) |-> Y
    );

endmodule