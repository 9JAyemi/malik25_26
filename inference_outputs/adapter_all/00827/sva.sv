module Test_sva (
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] out
);

    // When a is greater than or equal to b, out must equal a.
    check_out_matches_a_when_a_ge_b: assert property (
        @($global_clock) (a >= b) |-> (out == a)
    );

    // When b is greater than a, out must equal b.
    check_out_matches_b_when_b_gt_a: assert property (
        @($global_clock) (b > a) |-> (out == b)
    );

    // When a and b are equal, out must be zero.
    check_out_zero_when_a_eq_b: assert property (
        @($global_clock) (a == b) |-> (out == 8'h00)
    );

    // When a is greater than b, out must not equal a.
    check_out_not_a_when_a_gt_b: assert property (
        @($global_clock) (a > b) |-> (out != a)
    );

    // When b is greater than a, out must not equal b.
    check_out_not_b_when_b_gt_a: assert property (
        @($global_clock) (b > a) |-> (out != b)
    );

    // When a is greater than b, out must not be zero.
    check_out_not_zero_when_a_gt_b: assert property (
        @($global_clock) (a > b) |-> (out != 8'h00)
    );

    // When b is greater than a, out must not be zero.
    check_out_not_zero_when_b_gt_a: assert property (
        @($global_clock) (b > a) |-> (out != 8'h00)
    );

    // When a and b are equal, out must not equal a.
    check_out_not_a_when_a_eq_b: assert property (
        @($global_clock) (a == b) |-> (out != a)
    );

    // When a and b are equal, out must not equal b.
    check_out_not_b_when_a_eq_b: assert property (
        @($global_clock) (a == b) |-> (out != b)
    );

    // When a and b are equal, out must be zero.
    check_out_zero_when_a_eq_b: assert property (
        @($global_clock) (a == b) |-> (out == 8'h00)
    );

endmodule