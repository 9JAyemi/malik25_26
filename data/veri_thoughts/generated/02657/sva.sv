module top_module_sva (
    input logic clk,
    input logic d,
    input logic q
);

    ///// 3-cycle shift behavior /////
    // q equals d delayed by 3 cycles once history is available.
    check_three_cycle_delay: assert property (
        @(posedge clk) (!$isunknown($past(d,3))) |-> (q == $past(d,3))
    );

    // A rising edge on d is followed by a rising edge on q after 3 cycles.
    check_rise_propagates_3: assert property (
        @(posedge clk) $rose(d) |-> ##3 $rose(q)
    );

    // A falling edge on d is followed by a falling edge on q after 3 cycles.
    check_fall_propagates_3: assert property (
        @(posedge clk) $fell(d) |-> ##3 $fell(q)
    );

    // q changes only if d changed 3 cycles earlier (with sufficient history).
    check_q_change_requires_d_change_3ago: assert property (
        @(posedge clk) ($changed(q) && !$isunknown($past(d,3)) && !$isunknown($past(d,4))) |-> $past($changed(d),3)
    );

    // If d changed 3 cycles ago (with sufficient history), q must change now.
    check_d_change_3ago_causes_q_change: assert property (
        @(posedge clk) ($past($changed(d),3) && !$isunknown($past(d,3)) && !$isunknown($past(d,4))) |-> $changed(q)
    );

    // If d was unchanged between 4 and 3 cycles ago, q must be stable now.
    check_q_stable_when_past_d_unchanged: assert property (
        @(posedge clk) (!$isunknown($past(d,3)) && !$isunknown($past(d,4)) && ($past(d,3) == $past(d,4))) |-> $stable(q)
    );

endmodule