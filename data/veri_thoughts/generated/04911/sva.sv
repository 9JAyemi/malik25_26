module logic_function_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2
);

    // X must equal the AND of the two OR input groups.
    check_x_matches_or_and_function: assert property (
        @(posedge clk) X == ((A1 | A2) & (B1 | B2))
    );

    // If both A inputs are low, X must be low.
    check_a_group_low_forces_x_low: assert property (
        @(posedge clk) ((A1 == 1'b0) && (A2 == 1'b0)) |-> (X == 1'b0)
    );

    // If both B inputs are low, X must be low.
    check_b_group_low_forces_x_low: assert property (
        @(posedge clk) ((B1 == 1'b0) && (B2 == 1'b0)) |-> (X == 1'b0)
    );

    // If both OR groups are high, X must be high.
    check_both_or_groups_high_drive_x_high: assert property (
        @(posedge clk) ((A1 | A2) & (B1 | B2)) |-> (X == 1'b1)
    );

    // X high implies one A input and one B input are high.
    check_x_high_implies_both_groups_high: assert property (
        @(posedge clk) (X == 1'b1) |-> ((A1 | A2) & (B1 | B2))
    );

    // Stable sampled inputs must keep sampled X stable.
    check_stable_inputs_keep_x_stable: assert property (
        @(posedge clk) $stable({A1, A2, B1, B2}) |-> $stable(X)
    );

endmodule