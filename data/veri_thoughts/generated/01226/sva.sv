module calculation_module_sva (
    input logic [3:0] a,
    input logic [3:0] b,
    input logic c,
    input logic d,
    input logic e,
    input logic f
);
    // f implements the exact ternary-priority function of c,d,e and (a+b)[0].
    check_full_function: assert property (
        @($global_clock) disable iff (1'b0)
            f == (c ? 1'b1 : (d ? 1'b0 : (e ? 1'b1 : (a + b)[0])))
    );

    // If c is 1, f must be 1 (highest priority).
    check_c_priority_one: assert property (
        @($global_clock) disable iff (1'b0)
            (c == 1'b1) |-> (f == 1'b1)
    );

    // If c is 0 and d is 1, f must be 0 (d has priority over e).
    check_d_priority_zero_when_c0: assert property (
        @($global_clock) disable iff (1'b0)
            ((c == 1'b0) && (d == 1'b1)) |-> (f == 1'b0)
    );

    // If c is 0, d is 0, and e is 1, f must be 1.
    check_e_sets_one_when_cd0: assert property (
        @($global_clock) disable iff (1'b0)
            ((c == 1'b0) && (d == 1'b0) && (e == 1'b1)) |-> (f == 1'b1)
    );

    // If c, d, e are all 0, f equals LSB of (a + b).
    check_else_uses_sum_lsb: assert property (
        @($global_clock) disable iff (1'b0)
            ((c == 1'b0) && (d == 1'b0) && (e == 1'b0)) |-> (f == (a + b)[0])
    );

    // Under else branch, LSB of (a + b) equals a[0] XOR b[0].
    check_sum_lsb_equals_xor_in_else: assert property (
        @($global_clock) disable iff (1'b0)
            ((c == 1'b0) && (d == 1'b0) && (e == 1'b0)) |-> (f == (a[0] ^ b[0]))
    );

    // If c is 1 and d is also 1, c still forces f to 1 (priority over d).
    check_c_overrides_d: assert property (
        @($global_clock) disable iff (1'b0)
            ((c == 1'b1) && (d == 1'b1)) |-> (f == 1'b1)
    );

    // If c is 0 and both d and e are 1, d still forces f to 0 (priority over e).
    check_d_overrides_e_when_c0: assert property (
        @($global_clock) disable iff (1'b0)
            ((c == 1'b0) && (d == 1'b1) && (e == 1'b1)) |-> (f == 1'b0)
    );
endmodule