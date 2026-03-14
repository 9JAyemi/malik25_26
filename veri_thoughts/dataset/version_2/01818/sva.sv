module sky130_fd_sc_hvl__a22o_sva (
    input logic clk,   // sampling clock for SVA (design is purely combinational)
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2
);
    // X equals (A1 & A2) | (B1 & B2) each cycle.
    check_function_equation: assert property (
        @(posedge clk) X === ((A1 & A2) | (B1 & B2))
    );

    // If A1 & A2 is 1, X must be 1.
    check_a_pair_forces_x_high: assert property (
        @(posedge clk) ((A1 & A2) == 1'b1) |-> (X == 1'b1)
    );

    // If B1 & B2 is 1, X must be 1.
    check_b_pair_forces_x_high: assert property (
        @(posedge clk) ((B1 & B2) == 1'b1) |-> (X == 1'b1)
    );

    // If both (A1 & A2) and (B1 & B2) are 0, X must be 0.
    check_both_pairs_low_force_x_low: assert property (
        @(posedge clk) (((A1 & A2) == 1'b0) && ((B1 & B2) == 1'b0)) |-> (X == 1'b0)
    );

    // If X is 1, at least one pair (A1 & A2) or (B1 & B2) is 1.
    check_x_high_implies_one_pair_high: assert property (
        @(posedge clk) (X == 1'b1) |-> (((A1 & A2) == 1'b1) || ((B1 & B2) == 1'b1))
    );

    // If X is 0, both pairs (A1 & A2) and (B1 & B2) are 0.
    check_x_low_implies_both_pairs_low: assert property (
        @(posedge clk) (X == 1'b0) |-> (((A1 & A2) == 1'b0) && ((B1 & B2) == 1'b0))
    );

    // If inputs are stable across a cycle, X is stable across the cycle.
    check_stable_inputs_imply_stable_x: assert property (
        @(posedge clk) $stable({A1, A2, B1, B2}) |-> $stable(X)
    );

    // If A1 and B1 are 0, X must be 0 (both AND terms forced low).
    check_first_inputs_zero_force_x_low: assert property (
        @(posedge clk) ((A1 == 1'b0) && (B1 == 1'b0)) |-> (X == 1'b0)
    );

    // If A2 and B2 are 0, X must be 0 (both AND terms forced low).
    check_second_inputs_zero_force_x_low: assert property (
        @(posedge clk) ((A2 == 1'b0) && (B2 == 1'b0)) |-> (X == 1'b0)
    );
endmodule