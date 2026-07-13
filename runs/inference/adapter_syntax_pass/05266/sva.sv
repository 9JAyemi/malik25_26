module top_module_sva (
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] c,
    input logic [7:0] d,
    input logic [7:0] max
);

    // max must match the nested compare implemented in the RTL.
    check_max_matches_nested_compare: assert property (
        @($global_clock)
        max == ((a > b) ? a : b)
    );

    // max must equal a when a is greater than b.
    check_max_selects_a_when_a_gt_b: assert property (
        @($global_clock)
        (a > b) |-> (max == a)
    );

    // max must equal b when a is not greater than b.
    check_max_selects_b_when_a_le_b: assert property (
        @($global_clock)
        !(a > b) |-> (max == b)
    );

    // max must be at least a.
    check_max_is_at_least_a: assert property (
        @($global_clock)
        (max >= a)
    );

    // max must be at least b.
    check_max_is_at_least_b: assert property (
        @($global_clock)
        (max >= b)
    );

    // max must be at least the larger of a and b.
    check_max_is_at_least_max_of_a_b: assert property (
        @($global_clock)
        (max >= ((a > b) ? a : b))
    );

    // max must not exceed a.
    check_max_is_at_most_a: assert property (
        @($global_clock)
        (max <= a)
    );

    // max must not exceed b.
    check_max_is_at_most_b: assert property (
        @($global_clock)
        (max <= b)
    );

    // max must not exceed the larger of a and b.
    check_max_is_at_most_max_of_a_b: assert property (
        @($global_clock)
        (max <= ((a > b) ? a : b))
    );

endmodule