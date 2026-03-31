module top_module_sva (
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] c,
    input logic [7:0] d,
    input logic [7:0] max
);

    // max must match the nested comparator chain.
    check_max_matches_nested_chain: assert property (
        @($global_clock)
        max == ((a > b) ? ((a > c) ? ((a > d) ? a : d) : ((c > d) ? c : d)) : ((b > c) ? ((b > d) ? b : d) : ((c > d) ? c : d)))
    );

    // max must be at least a.
    check_max_ge_a: assert property (
        @($global_clock)
        max >= a
    );

    // max must be at least b.
    check_max_ge_b: assert property (
        @($global_clock)
        max >= b
    );

    // max must be at least c.
    check_max_ge_c: assert property (
        @($global_clock)
        max >= c
    );

    // max must be at least d.
    check_max_ge_d: assert property (
        @($global_clock)
        max >= d
    );

    // max must equal one of the inputs.
    check_max_is_one_of_inputs: assert property (
        @($global_clock)
        (max == a) || (max == b) || (max == c) || (max == d)
    );

    // If a is greater than or equal to all inputs, max must equal a.
    check_a_is_global_max: assert property (
        @($global_clock)
        (a >= b) && (a >= c) && (a >= d) |-> (max == a)
    );

    // If b is greater than or equal to all inputs, max must equal b.
    check_b_is_global_max: assert property (
        @($global_clock)
        (b >= a) && (b >= c) && (b >= d) |-> (max == b)
    );

    // If c is greater than or equal to all inputs, max must equal c.
    check_c_is_global_max: assert property (
        @($global_clock)
        (c >= a) && (c >= b) && (c >= d) |-> (max == c)
    );

    // If d is greater than or equal to all inputs, max must equal d.
    check_d_is_global_max: assert property (
        @($global_clock)
        (d >= a) && (d >= b) && (d >= c) |-> (max == d)
    );

    // If a and b are equal and greater than c and d, max must equal a.
    check_ab_equal_and_max: assert property (
        @($global_clock)
        (a == b) && (a >= c) && (a >= d) |-> (max == a)
    );

    // If a and c are equal and greater than b and d, max must equal a.
    check_ac_equal_and_max: assert property (
        @($global_clock)
        (a == c) && (a >= b) && (a >= d) |-> (max == a)
    );

    // If a and d are equal and greater than b and c, max must equal a.
    check_ad_equal_and_max: assert property (
        @($global_clock)
        (a == d) && (a >= b) && (a >= c) |-> (max == a)
    );

    // If b and c are equal and greater than a and d, max must equal b.
    check_bc_equal_and_max: assert property (
        @($global_clock)
        (b == c) && (b >= a) && (b >= d) |-> (max == b)
    );

    // If b and d are equal and greater than a and c, max must equal b.
    check_bd_equal_and_max: assert property (
        @($global_clock)
        (b == d) && (b >= a) && (b >= c) |-> (max == b)
    );

    // If c and d are equal and greater than a and b, max must equal c.
    check_cd_equal_and_max: assert property (
        @($global_clock)
        (c == d) && (c >= a) && (c >= b) |-> (max == c)
    );

endmodule