module top_module_sva (
    input logic a,
    input logic b,
    input logic sel_b1,
    input logic sel_b2,
    input logic out_always
);

    // No RTL clock or reset; sample combinational behavior on the formal global clock.

    // Output matches the composed half-adder and mux logic.
    check_overall_function: assert property (
        @($global_clock)
        out_always == ((sel_b1 & sel_b2) ? (a ^ b) : (a & b))
    );

    // When both selects are high, the mux passes the half-adder sum.
    check_selects_high_choose_sum: assert property (
        @($global_clock)
        (sel_b1 & sel_b2) |-> (out_always == (a ^ b))
    );

    // When either select is low, the mux passes the half-adder carry.
    check_not_both_selects_choose_carry: assert property (
        @($global_clock)
        !(sel_b1 & sel_b2) |-> (out_always == (a & b))
    );

    // If both inputs are low, the output must be low.
    check_zero_inputs_force_zero: assert property (
        @($global_clock)
        !(a | b) |-> (out_always == 1'b0)
    );

    // If exactly one input is high, the output follows the select conjunction.
    check_one_hot_inputs_follow_select_and: assert property (
        @($global_clock)
        (a ^ b) |-> (out_always == (sel_b1 & sel_b2))
    );

    // If both inputs are high, the output is the inverse of the select conjunction.
    check_both_inputs_high_invert_select_and: assert property (
        @($global_clock)
        (a & b) |-> (out_always == !(sel_b1 & sel_b2))
    );

endmodule