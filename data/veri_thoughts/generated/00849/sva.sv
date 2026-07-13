module min_finder_sva (
    input logic [7:0] a, b, c, d,
    input logic [7:0] min,
    input logic [7:0] ab_min, cd_min, global_min
);
    // Use a global formal clock for combinational design
    default clocking @(posedge $global_clock); endclocking

    // ab_min equals a when a < b
    check_ab_min_select_a: assert property (
        (a < b) |-> (ab_min == a)
    );

    // ab_min equals b when a >= b (ties choose b)
    check_ab_min_select_b: assert property (
        (a >= b) |-> (ab_min == b)
    );

    // ab_min is less than or equal to both a and b
    check_ab_min_le_inputs: assert property (
        (ab_min <= a) && (ab_min <= b)
    );

    // cd_min equals c when c < d
    check_cd_min_select_c: assert property (
        (c < d) |-> (cd_min == c)
    );

    // cd_min equals d when c >= d (ties choose d)
    check_cd_min_select_d: assert property (
        (c >= d) |-> (cd_min == d)
    );

    // cd_min is less than or equal to both c and d
    check_cd_min_le_inputs: assert property (
        (cd_min <= c) && (cd_min <= d)
    );

    // global_min equals ab_min when ab_min < cd_min
    check_global_min_select_ab: assert property (
        (ab_min < cd_min) |-> (global_min == ab_min)
    );

    // global_min equals cd_min when ab_min >= cd_min (ties choose cd_min)
    check_global_min_select_cd: assert property (
        (ab_min >= cd_min) |-> (global_min == cd_min)
    );

    // global_min is less than or equal to both ab_min and cd_min
    check_global_min_le_pair_mins: assert property (
        (global_min <= ab_min) && (global_min <= cd_min)
    );

    // Output min equals global_min
    check_min_equals_global_min: assert property (
        (min == global_min)
    );

    // Output min is less than or equal to all inputs
    check_min_le_all_inputs: assert property (
        (min <= a) && (min <= b) && (min <= c) && (min <= d)
    );

    // Output min equals one of the inputs
    check_min_is_one_of_inputs: assert property (
        (min == a) || (min == b) || (min == c) || (min == d)
    );
endmodule