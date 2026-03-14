module top_module_sva (
    input logic CLK,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic SUBTRACT,
    input logic [3:0] SUM,
    input logic OVERFLOW,
    input logic EQUAL,
    input logic GREATER_THAN,
    input logic LESS_THAN
);
    ///// SUM behavior /////
    // When not subtracting, SUM equals A + B (4-bit wrap).
    check_sum_add: assert property (
        @(posedge CLK) (!SUBTRACT) |-> (SUM == (A + B))
    );
    // When subtracting, SUM equals A + (~B) + 1 (two's complement, 4-bit wrap).
    check_sum_sub: assert property (
        @(posedge CLK) (SUBTRACT) |-> (SUM == (A + (~B) + 4'b0001))
    );
    // When subtracting and A == B, SUM is zero.
    check_sum_sub_equal_zero: assert property (
        @(posedge CLK) (SUBTRACT && (A == B)) |-> (SUM == 4'b0000)
    );

    ///// Comparator flags (EQUAL/GREATER_THAN/LESS_THAN) /////
    // Comparator flags are one-hot.
    check_compare_onehot: assert property (
        @(posedge CLK) $onehot({EQUAL, GREATER_THAN, LESS_THAN})
    );
    // If A == B, only EQUAL is asserted.
    check_equal_when_AeqB: assert property (
        @(posedge CLK) (A == B) |-> (EQUAL && !GREATER_THAN && !LESS_THAN)
    );
    // If EQUAL is asserted, then A == B.
    check_AeqB_when_equal: assert property (
        @(posedge CLK) (EQUAL) |-> (A == B)
    );
    // If A > B, only GREATER_THAN is asserted.
    check_gt_when_AgtB: assert property (
        @(posedge CLK) (A > B) |-> (GREATER_THAN && !EQUAL && !LESS_THAN)
    );
    // If GREATER_THAN is asserted, then A > B.
    check_AgtB_when_gt: assert property (
        @(posedge CLK) (GREATER_THAN) |-> (A > B)
    );
    // If A < B, only LESS_THAN is asserted.
    check_lt_when_AltB: assert property (
        @(posedge CLK) (A < B) |-> (LESS_THAN && !EQUAL && !GREATER_THAN)
    );
    // If LESS_THAN is asserted, then A < B.
    check_AltB_when_lt: assert property (
        @(posedge CLK) (LESS_THAN) |-> (A < B)
    );
endmodule