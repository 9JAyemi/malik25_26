module top_module_sva (
    input logic clk,
    input logic d,
    input logic q
);
    // q equals d sampled at the previous posedge.
    check_q_matches_prev_d: assert property (
        @(posedge clk) disable iff ($initstate) q == $past(d)
    );

    // On the next posedge, q equals d from the current posedge.
    check_q_next_matches_curr_d: assert property (
        @(posedge clk) disable iff ($initstate) ##1 (q == $past(d))
    );

    // If d is stable this cycle, q is stable next cycle.
    check_d_stable_implies_q_stable_next: assert property (
        @(posedge clk) disable iff ($initstate) $stable(d) |-> ##1 $stable(q)
    );

    // If d changes this cycle, q changes next cycle.
    check_d_change_implies_q_change_next: assert property (
        @(posedge clk) disable iff ($initstate) $changed(d) |-> ##1 $changed(q)
    );

    // If q changes this cycle, d changed in the previous cycle.
    check_q_change_implies_d_change_prev: assert property (
        @(posedge clk) disable iff ($initstate) $changed(q) |-> $past($changed(d))
    );

    // If d is stable this cycle, q equals d now.
    check_d_stable_implies_q_equals_d_now: assert property (
        @(posedge clk) disable iff ($initstate) $stable(d) |-> (q == d)
    );

    // If d rises at this posedge, q is LOW now (reflecting prior d).
    check_rose_d_implies_q_low_now: assert property (
        @(posedge clk) disable iff ($initstate) $rose(d) |-> (q == 1'b0)
    );

    // If d falls at this posedge, q is HIGH now (reflecting prior d).
    check_fell_d_implies_q_high_now: assert property (
        @(posedge clk) disable iff ($initstate) $fell(d) |-> (q == 1'b1)
    );

    // If d rises at this posedge, q is HIGH at the next posedge.
    check_rose_d_implies_q_high_next: assert property (
        @(posedge clk) disable iff ($initstate) $rose(d) |-> ##1 (q == 1'b1)
    );

    // If d falls at this posedge, q is LOW at the next posedge.
    check_fell_d_implies_q_low_next: assert property (
        @(posedge clk) disable iff ($initstate) $fell(d) |-> ##1 (q == 1'b0)
    );
endmodule