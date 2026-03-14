module DFF_sva (
    input logic q,
    input logic d,
    input logic ck
);
    // q must equal d from the previous rising edge (1-cycle latency).
    check_q_updates_from_prev_d: assert property (
        @(posedge ck) !$isunknown($past(d)) |-> (q == $past(d))
    );

    // If d did not change across the last two cycles, q did not change in the last cycle.
    check_q_stable_when_prev_d_stable: assert property (
        @(posedge ck) (!$isunknown($past(d)) && !$isunknown($past(d,2)) && !$isunknown(q) && !$isunknown($past(q)) && ($past(d) == $past(d,2))) |-> (q == $past(q))
    );

    // q change between this and last cycle matches d change between the previous two cycles.
    check_q_change_matches_prev_d_change: assert property (
        @(posedge ck) (!$isunknown($past(d)) && !$isunknown($past(d,2)) && !$isunknown(q) && !$isunknown($past(q))) |-> ($changed(q) == ($past(d) != $past(d,2)))
    );

    // If d toggled at this edge, q must differ from d (since q reflects previous d).
    check_q_differs_from_d_when_d_toggled: assert property (
        @(posedge ck) (!$isunknown(d) && !$isunknown($past(d)) && (d != $past(d))) |-> (q != d)
    );

    // If d is stable across this edge, q must equal d at this edge.
    check_q_equals_d_when_d_stable: assert property (
        @(posedge ck) (!$isunknown(d) && !$isunknown($past(d)) && (d == $past(d))) |-> (q == d)
    );

    // On the next rising edge, q must equal the current d value (restating 1-cycle latency).
    check_next_cycle_q_matches_current_d: assert property (
        @(posedge ck) !$isunknown(d) |-> ##1 (q == $past(d))
    );
endmodule