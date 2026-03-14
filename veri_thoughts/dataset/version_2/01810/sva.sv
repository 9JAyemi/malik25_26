module d_ff_async_set_reset_sva (
    input logic clk,
    input logic reset,   // active-LOW
    input logic set,     // active-LOW
    input logic d,
    input logic q,
    input logic q_bar
);
    // Reset low drives q=0, q_bar=1 on next cycle.
    check_reset_forces_outputs: assert property (
        @(posedge clk) (reset == 1'b0) |=> (q == 1'b0 && q_bar == 1'b1)
    );

    // Set low (with reset high) drives q=1, q_bar=0 on next cycle.
    check_set_forces_outputs: assert property (
        @(posedge clk) disable iff (reset == 1'b0)
            (set == 1'b0) |=> (q == 1'b1 && q_bar == 1'b0)
    );

    // With reset and set both high, capture d into q and ~d into q_bar on next cycle.
    check_data_capture: assert property (
        @(posedge clk) disable iff (reset == 1'b0)
            (set == 1'b1) |=> (q == $past(d) && q_bar == ~$past(d))
    );

    // q_bar is always the complement of q.
    check_outputs_complement: assert property (
        @(posedge clk) (q_bar == ~q)
    );

    // If reset is held low across consecutive cycles, outputs stay q=0, q_bar=1.
    check_hold_under_reset: assert property (
        @(posedge clk) ($past(reset) == 1'b0 && reset == 1'b0) |-> (q == 1'b0 && q_bar == 1'b1)
    );

    // If set is held low with reset high across consecutive cycles, outputs stay q=1, q_bar=0.
    check_hold_under_set: assert property (
        @(posedge clk) disable iff (reset == 1'b0)
            ($past(reset) == 1'b1 && reset == 1'b1 && $past(set) == 1'b0 && set == 1'b0) |-> (q == 1'b1 && q_bar == 1'b0)
    );

    // If both reset and set remain high across cycles, outputs reflect prior d each cycle.
    check_hold_under_normal: assert property (
        @(posedge clk) disable iff (reset == 1'b0)
            ($past(reset) == 1'b1 && reset == 1'b1 && $past(set) == 1'b1 && set == 1'b1) |-> (q == $past(d) && q_bar == ~$past(d))
    );

    // Reset has priority over set when both are low.
    check_reset_priority_over_set: assert property (
        @(posedge clk) (reset == 1'b0 && set == 1'b0) |=> (q == 1'b0 && q_bar == 1'b1)
    );

    // In normal mode, if d differs from previous q, q toggles next cycle.
    check_data_change_causes_q_toggle: assert property (
        @(posedge clk) disable iff (reset == 1'b0)
            (set == 1'b1 && d != $past(q)) |=> (q != $past(q))
    );

    // In normal mode, if d equals previous q, q holds next cycle.
    check_data_same_keeps_q: assert property (
        @(posedge clk) disable iff (reset == 1'b0)
            (set == 1'b1 && d == $past(q)) |=> (q == $past(q))
    );

endmodule