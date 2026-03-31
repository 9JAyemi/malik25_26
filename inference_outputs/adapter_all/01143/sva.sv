module dual_edge_triggered_ff_sva (
    input logic clk,
    input logic d,
    input logic q
);

    // q reflects the d value sampled on the previous falling edge.
    check_q_matches_prev_falling_edge_d: assert property (
        @(negedge clk) disable iff ($initstate) q == $past(d, 1, @(negedge clk))
    );

    // A rising edge on q must come from a rising edge on d at the prior falling edge.
    check_q_rise_requires_prev_falling_edge_d_rise: assert property (
        @(negedge clk) disable iff ($initstate) $rose(q) |-> $past($rose(d), 1, @(negedge clk))
    );

    // A falling edge on q must come from a falling edge on d at the prior falling edge.
    check_q_fall_requires_prev_falling_edge_d_fall: assert property (
        @(negedge clk) disable iff ($initstate) $fell(q) |-> $past($fell(d), 1, @(negedge clk))
    );

    // If d is stable across consecutive falling edges, q is stable across those edges.
    check_q_stable_when_d_stable: assert property (
        @(negedge clk) disable iff ($initstate) $stable(d) |-> $stable(q)
    );

    // If d changes between consecutive falling edges, q changes between those edges.
    check_q_changes_when_d_changes: assert property (
        @(negedge clk) disable iff ($initstate) !$stable(d) |-> !$stable(q)
    );

    // A rising edge on d at a falling edge causes q to rise at the next falling edge.
    check_prev_falling_edge_d_rise_causes_q_rise: assert property (
        @(negedge clk) disable iff ($initstate) $rose(d) |-> ##1 $rose(q)
    );

    // A falling edge on d at a falling edge causes q to fall at the next falling edge.
    check_prev_falling_edge_d_fall_causes_q_fall: assert property (
        @(negedge clk) disable iff ($initstate) $fell(d) |-> ##1 $fell(q)
    );

endmodule