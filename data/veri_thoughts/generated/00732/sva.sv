module my_module_sva (
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic C1,
    input logic X
);
    // X implements the exact RTL expression.
    check_x_matches_rtl_expr: assert property (
        @(posedge B1) X === (A1 | (A2 & !A1) | (A3 & !A2 & !A1))
    );

    // X equals the OR of A1, A2, A3 (algebraic simplification).
    check_x_equals_or_of_three: assert property (
        @(posedge B1) X === (A1 | A2 | A3)
    );

    // If all A inputs are 0, X must be 0.
    check_x_zero_when_all_zero: assert property (
        @(posedge B1) ((A1 == 1'b0) && (A2 == 1'b0) && (A3 == 1'b0)) |-> (X == 1'b0)
    );

    // If X is 1, at least one A input must be 1.
    check_x_one_implies_some_a_high: assert property (
        @(posedge B1) (X == 1'b1) |-> ((A1 == 1'b1) || (A2 == 1'b1) || (A3 == 1'b1))
    );

    // If X is 0, all A inputs must be 0.
    check_x_zero_implies_all_a_low: assert property (
        @(posedge B1) (X == 1'b0) |-> ((A1 == 1'b0) && (A2 == 1'b0) && (A3 == 1'b0))
    );

    // With only A1 high, X must be 1.
    check_x_one_when_only_a1_high: assert property (
        @(posedge B1) ((A1 == 1'b1) && (A2 == 1'b0) && (A3 == 1'b0)) |-> (X == 1'b1)
    );

    // With only A2 high, X must be 1.
    check_x_one_when_only_a2_high: assert property (
        @(posedge B1) ((A1 == 1'b0) && (A2 == 1'b1) && (A3 == 1'b0)) |-> (X == 1'b1)
    );

    // With only A3 high, X must be 1.
    check_x_one_when_only_a3_high: assert property (
        @(posedge B1) ((A1 == 1'b0) && (A2 == 1'b0) && (A3 == 1'b1)) |-> (X == 1'b1)
    );
endmodule