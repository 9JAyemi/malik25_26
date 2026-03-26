module Comparator_sva (
    input logic        clk,
    input logic [7:0]  A,
    input logic [7:0]  B,
    input logic        EQ,
    input logic        GT,
    input logic        LT
);

    // EQ must reflect equality of A and B.
    check_eq_definition: assert property (
        @(posedge clk) EQ == (A == B)
    );

    // GT must reflect unsigned greater-than of A over B.
    check_gt_definition: assert property (
        @(posedge clk) GT == (A > B)
    );

    // LT must reflect unsigned less-than of A under B.
    check_lt_definition: assert property (
        @(posedge clk) LT == (A < B)
    );

    // EQ and GT cannot be high together.
    check_eq_excludes_gt: assert property (
        @(posedge clk) !(EQ && GT)
    );

    // EQ and LT cannot be high together.
    check_eq_excludes_lt: assert property (
        @(posedge clk) !(EQ && LT)
    );

    // GT and LT cannot be high together.
    check_gt_excludes_lt: assert property (
        @(posedge clk) !(GT && LT)
    );

    // One comparison result must always be true.
    check_total_order_covered: assert property (
        @(posedge clk) (EQ || GT || LT)
    );

    // Equal inputs must drive only EQ high.
    check_equal_case_outputs: assert property (
        @(posedge clk) (A == B) |-> (EQ && !GT && !LT)
    );

    // A greater than B must drive only GT high.
    check_greater_case_outputs: assert property (
        @(posedge clk) (A > B) |-> (GT && !EQ && !LT)
    );

    // A less than B must drive only LT high.
    check_less_case_outputs: assert property (
        @(posedge clk) (A < B) |-> (LT && !EQ && !GT)
    );

endmodule