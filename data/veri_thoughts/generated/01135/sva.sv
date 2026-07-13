module d_flip_flop_sva (
    input logic clk,
    input logic d,
    input logic q
);

    // Q equals the value of D from the previous clock edge (one-cycle latency).
    check_q_equals_past_d: assert property (
        @(posedge clk) $past(1'b1) |-> (q == $past(d))
    );

    // If D was stable across the last two cycles, Q holds its value this cycle.
    check_q_stable_when_d_held: assert property (
        @(posedge clk) ($past(1'b1,2) && ($past(d) == $past(d,2))) |-> (q == $past(q))
    );

    // If D changed between the last two cycles, Q changes accordingly this cycle.
    check_q_changes_when_d_changes: assert property (
        @(posedge clk) ($past(1'b1,2) && ($past(d) != $past(d,2))) |-> (q != $past(q))
    );

    // The current D value is observed on Q at the next clock edge.
    check_next_cycle_transfer: assert property (
        @(posedge clk) 1'b1 |=> (q == $past(d))
    );

    // Whenever Q changes, its new value equals the previously sampled D.
    check_q_change_matches_prev_d: assert property (
        @(posedge clk) ($past(1'b1,2) && (q != $past(q))) |-> (q == $past(d))
    );

endmodule