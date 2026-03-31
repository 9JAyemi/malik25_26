module top_module_sva (
    input logic clk,
    input logic [7:0] d,
    input logic [7:0] q
);
    // q equals d sampled on the previous negedge (1-cycle latency).
    check_q_equals_prev_d: assert property (
        @(negedge clk) q == $past(d)
    );

    // If d changes between negedges, q changes on the next negedge.
    check_q_changes_when_d_changes: assert property (
        @(negedge clk) $changed(d) |=> $changed(q)
    );

    // If d is stable between negedges, q is stable on the next negedge.
    check_q_stable_when_d_stable: assert property (
        @(negedge clk) $stable(d) |=> $stable(q)
    );

    // Any change on q must be caused by a change on d in the prior cycle.
    check_q_change_requires_d_change: assert property (
        @(negedge clk) $changed(q) |-> $changed(d)
    );

    // If d changes between negedges, q equals the prior d on the next negedge.
    check_q_matches_prev_d_on_d_change: assert property (
        @(negedge clk) $changed(d) |=> (q == $past(d))
    );

    // If d is stable between negedges, q equals the prior d on the next negedge.
    check_q_matches_prev_d_on_d_stable: assert property (
        @(negedge clk) $stable(d) |=> (q == $past(d))
    );

    // If d changes between negedges, q differs from the current d on the next negedge.
    check_q_differs_from_current_d_on_d_change: assert property (
        @(negedge clk) $changed(d) |=> (q != d)
    );

    // If d is stable between negedges, q differs from the current d on the next negedge.
    check_q_differs_from_current_d_on_d_stable: assert property (
        @(negedge clk) $stable(d) |=> (q != d)
    );

    // If d changes between negedges, q equals the prior d on the next negedge (repeated check).
    check_q_matches_prev_d_on_d_change_repeat: assert property (
        @(negedge clk) $changed(d) |=> (q == $past(d))
    );

    // If d is stable between negedges, q equals the prior d on the next negedge (repeated check).
    check_q_matches_prev_d_on_d_stable_repeat: assert property (
        @(negedge clk) $stable(d) |=> (q == $past(d))
    );
endmodule