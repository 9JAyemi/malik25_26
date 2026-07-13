module nor4bb_sva (
    input logic clk,
    input logic Y,
    input logic A,
    input logic B,
    input logic C_N,
    input logic D_N
);

    // Y equals the implemented 4-input NOR.
    check_y_matches_nor_logic: assert property (
        @(posedge clk) Y == ~(A | B | C_N | D_N)
    );

    // All-low inputs drive Y high.
    check_all_inputs_low_set_y_high: assert property (
        @(posedge clk) (!A && !B && !C_N && !D_N) |-> (Y == 1'b1)
    );

    // A high drives Y low.
    check_a_high_forces_y_low: assert property (
        @(posedge clk) A |-> (Y == 1'b0)
    );

    // B high drives Y low.
    check_b_high_forces_y_low: assert property (
        @(posedge clk) B |-> (Y == 1'b0)
    );

    // C_N high drives Y low.
    check_cn_high_forces_y_low: assert property (
        @(posedge clk) C_N |-> (Y == 1'b0)
    );

    // D_N high drives Y low.
    check_dn_high_forces_y_low: assert property (
        @(posedge clk) D_N |-> (Y == 1'b0)
    );

    // Y high requires all inputs low.
    check_y_high_implies_all_inputs_low: assert property (
        @(posedge clk) Y |-> (!A && !B && !C_N && !D_N)
    );

    // Y low requires at least one input high.
    check_y_low_implies_some_input_high: assert property (
        @(posedge clk) !Y |-> (A || B || C_N || D_N)
    );

endmodule