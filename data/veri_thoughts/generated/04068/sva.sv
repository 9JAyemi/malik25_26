module largest_of_three_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic X
);

    // X must match the implemented comparison behavior.
    check_output_matches_implemented_logic: assert property (
        @(posedge clk)
        X == ((A > C) ? 1'b1 : 1'b0)
    );

    // A high and C low must drive X high.
    check_output_high_when_a_high_c_low: assert property (
        @(posedge clk)
        ((A == 1'b1) && (C == 1'b0)) |-> (X == 1'b1)
    );

    // X can only be high when A is high and C is low.
    check_output_high_only_for_a_gt_c: assert property (
        @(posedge clk)
        (X == 1'b1) |-> ((A == 1'b1) && (C == 1'b0))
    );

    // When C is low, X must track A.
    check_output_tracks_a_when_c_low: assert property (
        @(posedge clk)
        (C == 1'b0) |-> (X == A)
    );

    // When A is high, X must be the inverse of C.
    check_output_tracks_inverse_c_when_a_high: assert property (
        @(posedge clk)
        (A == 1'b1) |-> (X == ~C)
    );

    // If A is low or C is high, X must be low.
    check_output_low_when_not_a_gt_c: assert property (
        @(posedge clk)
        ((A == 1'b0) || (C == 1'b1)) |-> (X == 1'b0)
    );

endmodule