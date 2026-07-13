module Test_sva (
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] out
);

    // out must match the RTL's conditional selection.
    check_out_matches_rtl: assert property (
        @($global_clock) out == ((a >= b) ? a : b)
    );

    // When a is greater than or equal to b, out must equal a.
    check_out_equals_a_when_a_ge_b: assert property (
        @($global_clock) (a >= b) |-> (out == a)
    );

    // When b is greater than a, out must equal b.
    check_out_equals_b_when_b_gt_a: assert property (
        @($global_clock) (b > a) |-> (out == b)
    );

    // When a and b are equal, out must equal that common value.
    check_out_equals_common_value_when_equal: assert property (
        @($global_clock) (a == b) |-> (out == a)
    );

    // When a is less than b, out must equal b.
    check_out_equals_b_when_a_lt_b: assert property (
        @($global_clock) (a < b) |-> (out == b)
    );

endmodule