module dual_edge_triggered_flip_flop_sva (
    input logic clk,
    input logic d,
    input logic q
);
    // Clock: clk (posedge). No reset present. q is d delayed by 2 cycles.

    // Q equals D delayed by exactly 2 clock cycles.
    check_q_two_cycle_delay: assert property (
        @(posedge clk) 1'b1 |-> ##2 (q == $past(d, 2))
    );

    // A rising edge on D causes a rising edge on Q two cycles later.
    check_d_rise_to_q_rise_two: assert property (
        @(posedge clk) $rose(d) |-> ##2 $rose(q)
    );

    // A falling edge on D causes a falling edge on Q two cycles later.
    check_d_fall_to_q_fall_two: assert property (
        @(posedge clk) $fell(d) |-> ##2 $fell(q)
    );

    // Any change on D propagates to Q two cycles later.
    check_d_change_to_q_change_two: assert property (
        @(posedge clk) $changed(d) |-> ##2 $changed(q)
    );

    // If D is stable over a cycle, Q is stable two cycles later.
    check_d_stable_implies_q_stable_two: assert property (
        @(posedge clk) $stable(d) |-> ##2 $stable(q)
    );

    // Q changes only if D changed two cycles earlier.
    check_q_change_implies_prior_d_change: assert property (
        @(posedge clk) $changed(q) |-> ($past(d, 2) != $past(d, 3))
    );

    // Q stable only if D was stable two and three cycles earlier.
    check_q_stable_implies_prior_d_stable: assert property (
        @(posedge clk) $stable(q) |-> ($past(d, 2) == $past(d, 3))
    );

    // A rising edge on Q corresponds to D=1 two cycles earlier and D=0 three cycles earlier.
    check_q_rise_matches_prior_d: assert property (
        @(posedge clk) $rose(q) |-> ($past(d, 2) == 1'b1 && $past(d, 3) == 1'b0)
    );

    // A falling edge on Q corresponds to D=0 two cycles earlier and D=1 three cycles earlier.
    check_q_fall_matches_prior_d: assert property (
        @(posedge clk) $fell(q) |-> ($past(d, 2) == 1'b0 && $past(d, 3) == 1'b1)
    );

    // Equivalence: Q changes iff D differed two and three cycles earlier.
    check_q_change_equivalence: assert property (
        @(posedge clk) ($changed(q) == ($past(d, 2) != $past(d, 3)))
    );
endmodule