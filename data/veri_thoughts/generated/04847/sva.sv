module t_assertions (
    input logic reset,
    input logic a,
    input logic b,
    input logic c,
    input logic en,
    input logic o1,
    input logic o2,
    input logic o3,
    input logic o4,
    input logic o5
);

    // A c-only change does not trigger this process.
    check_c_only_change_holds_outputs: assert property (
        @($global_clock) disable iff ($initstate)
        ($changed(c) && !$changed(reset) && !$changed(en) && !$changed(a) && !$changed(b))
        |-> $stable({o1, o2, o3, o4, o5})
    );

    // Any evaluation while reset is high clears all outputs.
    check_reset_clears_outputs: assert property (
        @($global_clock) disable iff ($initstate)
        (($changed(reset) || $changed(en) || $changed(a) || $changed(b)) && reset)
        |-> (o1 == 1'b0 && o2 == 1'b0 && o3 == 1'b0 && o4 == 1'b0 && o5 == 1'b0)
    );

    // Any non-reset evaluation drives o1 high.
    check_o1_high_out_of_reset: assert property (
        @($global_clock) disable iff (reset || $initstate)
        ($changed(reset) || $changed(en) || $changed(a) || $changed(b))
        |-> (o1 == 1'b1)
    );

    // Any non-reset evaluation leaves o2 high.
    check_o2_high_out_of_reset: assert property (
        @($global_clock) disable iff (reset || $initstate)
        ($changed(reset) || $changed(en) || $changed(a) || $changed(b))
        |-> (o2 == 1'b1)
    );

    // With en high, o3 is driven high.
    check_en_branch_o3_high: assert property (
        @($global_clock) disable iff (reset || $initstate)
        (($changed(reset) || $changed(en) || $changed(a) || $changed(b)) && en)
        |-> (o3 == 1'b1)
    );

    // With en high, o5 follows a.
    check_en_branch_o5_matches_a: assert property (
        @($global_clock) disable iff (reset || $initstate)
        (($changed(reset) || $changed(en) || $changed(a) || $changed(b)) && en)
        |-> (o5 == a)
    );

    // With en high, o4 follows the c-selected assignment.
    check_en_branch_o4_function: assert property (
        @($global_clock) disable iff (reset || $initstate)
        (($changed(reset) || $changed(en) || $changed(a) || $changed(b)) && en)
        |-> (o4 == (c ? 1'b1 : ((~a) ^ b)))
    );

    // With en low, o3 matches a OR b.
    check_dis_branch_o3_function: assert property (
        @($global_clock) disable iff (reset || $initstate)
        (($changed(reset) || $changed(en) || $changed(a) || $changed(b)) && !en)
        |-> (o3 == (a | b))
    );

    // With en low, o4 is driven low.
    check_dis_branch_o4_low: assert property (
        @($global_clock) disable iff (reset || $initstate)
        (($changed(reset) || $changed(en) || $changed(a) || $changed(b)) && !en)
        |-> (o4 == 1'b0)
    );

    // With en low and b high, o5 is driven low.
    check_dis_branch_b_high_o5_low: assert property (
        @($global_clock) disable iff (reset || $initstate)
        (($changed(reset) || $changed(en) || $changed(a) || $changed(b)) && !en && b)
        |-> (o5 == 1'b0)
    );

    // With en low and b low, o5 keeps its previous value.
    check_dis_branch_b_low_o5_holds: assert property (
        @($global_clock) disable iff (reset || $initstate)
        (($changed(reset) || $changed(en) || $changed(a) || $changed(b)) && !en && !b)
        |-> (o5 == $past(o5))
    );

endmodule