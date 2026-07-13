module comparator_sva (
    input logic [31:0] a,
    input logic [31:0] b,
    input logic unsigned_cmp,
    input logic greater,
    input logic less,
    input logic equal,
    input logic clk
);

    // Exactly one comparison result flag is asserted.
    check_result_onehot: assert property (
        @(posedge clk)
        (greater || less || equal) &&
        !(greater && less) &&
        !(greater && equal) &&
        !(less && equal)
    );

    // Equal is asserted iff the operands are identical.
    check_equal_matches_operands: assert property (
        @(posedge clk)
        equal == (a == b)
    );

    // In unsigned mode, outputs match the unsigned comparison.
    check_unsigned_mode_behavior: assert property (
        @(posedge clk)
        unsigned_cmp |-> (
            (greater == (a > b)) &&
            (less == (a < b)) &&
            (equal == (a == b))
        )
    );

    // In signed mode, a negative a is less than a non-negative b.
    check_signed_diff_sign_negative_a: assert property (
        @(posedge clk)
        (!unsigned_cmp && (a[31] != b[31]) && a[31]) |-> (!greater && less && !equal)
    );

    // In signed mode, a non-negative a is greater than a negative b.
    check_signed_diff_sign_positive_a: assert property (
        @(posedge clk)
        (!unsigned_cmp && (a[31] != b[31]) && !a[31]) |-> (greater && !less && !equal)
    );

    // In signed mode with equal sign bits, outputs match the magnitude comparison.
    check_signed_same_sign_behavior: assert property (
        @(posedge clk)
        (!unsigned_cmp && (a[31] == b[31])) |-> (
            (greater == (a > b)) &&
            (less == (a < b)) &&
            (equal == (a == b))
        )
    );

endmodule