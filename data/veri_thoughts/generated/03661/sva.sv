module max_value_sva (
    input logic a,
    input logic b,
    input logic c,
    input logic out
);

    // No RTL clock or reset; sample this pure combinational logic on $global_clock.

    // out must match the exact RTL max-selection expression.
    check_function_matches_rtl: assert property (
        @($global_clock)
        out == ((a > b) ? ((a > c) ? a : c) : ((b > c) ? b : c))
    );

    // If a is greater than both b and c, out must select a.
    check_select_a_when_a_is_largest: assert property (
        @($global_clock)
        ((a > b) && (a > c)) |-> (out == a)
    );

    // If a is greater than b but not greater than c, out must select c.
    check_select_c_when_c_beats_a_in_a_branch: assert property (
        @($global_clock)
        ((a > b) && !(a > c)) |-> (out == c)
    );

    // If a is not greater than b and b is greater than c, out must select b.
    check_select_b_when_b_is_largest_in_else_branch: assert property (
        @($global_clock)
        (!(a > b) && (b > c)) |-> (out == b)
    );

    // If a is not greater than b and b is not greater than c, out must select c.
    check_select_c_when_c_wins_else_branch: assert property (
        @($global_clock)
        (!(a > b) && !(b > c)) |-> (out == c)
    );

endmodule