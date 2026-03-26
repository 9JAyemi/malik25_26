module magnitude_comparator_sva (
    input logic       clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       EQ,
    input logic       GT,
    input logic       LT
);

    // Combinational comparator with no reset; clk is an external sampling clock for SVA.

    // EQ must match whether A and B are equal.
    check_eq_definition: assert property (
        @(posedge clk) EQ === (A == B)
    );

    // GT must match whether A is greater than B.
    check_gt_definition: assert property (
        @(posedge clk) GT === (A > B)
    );

    // LT must match whether A is less than B.
    check_lt_definition: assert property (
        @(posedge clk) LT === (A < B)
    );

    // Equal inputs must drive only EQ high.
    check_equal_case_outputs: assert property (
        @(posedge clk) ((A == B) === 1'b1) |-> (EQ && !GT && !LT)
    );

    // A greater than B must drive only GT high.
    check_greater_case_outputs: assert property (
        @(posedge clk) ((A > B) === 1'b1) |-> (GT && !EQ && !LT)
    );

    // A less than B must drive only LT high.
    check_less_case_outputs: assert property (
        @(posedge clk) ((A < B) === 1'b1) |-> (LT && !EQ && !GT)
    );

endmodule