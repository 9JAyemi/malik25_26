module top_module_sva (
    input logic clk,
    input logic d,
    input logic q
);

    // q must not change exactly at a rising edge (updates only occur on negedge in RTL).
    check_no_q_update_at_posedge: assert property (
        @(posedge clk) !$changed(q)
    );

    // On each falling edge after at least one prior rising edge, q equals d sampled at that prior rising edge.
    check_q_from_prev_posedge_d: assert property (
        @(negedge clk) $past(1'b1, 1, posedge clk) |-> (q == $past(d, 1, posedge clk))
    );

    // If d is unchanged across two consecutive rising edges, q is unchanged across the corresponding falling edges.
    check_q_stable_when_d_stable_posedges: assert property (
        @(negedge clk)
            ($past(1'b1) && $past(1'b1, 2, posedge clk) &&
             ($past(d, 1, posedge clk) == $past(d, 2, posedge clk)))
            |-> (q == $past(q))
    );

    // If d changes between two consecutive rising edges, q must change at the following falling edge.
    check_q_change_when_d_changes_posedges: assert property (
        @(negedge clk)
            ($past(1'b1) && $past(1'b1, 2, posedge clk) &&
             ($past(d, 1, posedge clk) != $past(d, 2, posedge clk)))
            |-> $changed(q)
    );

    // If q changes at a falling edge, then d must have changed between the last two rising edges.
    check_q_change_implies_d_change_between_posedges: assert property (
        @(negedge clk)
            ($past(1'b1) && $past(1'b1, 2, posedge clk) && $changed(q))
            |-> ($past(d, 1, posedge clk) != $past(d, 2, posedge clk))
    );

    // At a falling edge, if d differs from the last rising-edge sample, q must differ from the current d.
    check_q_not_equal_current_d_if_intermediate_change: assert property (
        @(negedge clk)
            ($past(1'b1, 1, posedge clk) && (d != $past(d, 1, posedge clk)))
            |-> (q != d)
    );

    // At a falling edge, if d equals the last rising-edge sample, q must equal the current d.
    check_q_equal_current_d_if_matches_sample: assert property (
        @(negedge clk)
            ($past(1'b1, 1, posedge clk) && (d == $past(d, 1, posedge clk)))
            |-> (q == d)
    );

endmodule