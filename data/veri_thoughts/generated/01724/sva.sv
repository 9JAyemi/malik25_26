module dual_edge_ff_sva (
    input logic clk,
    input logic d,
    input logic q
);
    // Clock: clk (both posedge and negedge used). Reset: none.
    // Logic: sequential across both edges; q updates on negedge to prior posedge d.

    // On each negedge, q equals d captured at the most recent posedge.
    check_q_eq_prev_posedge_d_at_negedge: assert property (
        @(negedge clk) q == $past(d, 1, posedge clk)
    );

    // On each posedge, q still equals d from the previous posedge.
    check_q_eq_prev_posedge_d_at_posedge: assert property (
        @(posedge clk) q == $past(d)
    );

    // If q changes at a negedge, then d must have changed at the preceding posedge vs. the one before it.
    check_q_change_at_negedge_implies_d_change: assert property (
        @(negedge clk) $changed(q) |-> ($past(d, 1, posedge clk) != $past(d, 2, posedge clk))
    );

    // If d changed at the current posedge vs. the prior posedge, q must change at this negedge.
    check_d_change_at_posedge_implies_q_change: assert property (
        @(negedge clk) ($past(d, 1, posedge clk) != $past(d, 2, posedge clk)) |-> (q != $past(q))
    );

    // If d did not change across the last two posedges, q must be stable across the last two negedges.
    check_q_stable_when_d_stable_across_posedges: assert property (
        @(negedge clk) ($past(d, 1, posedge clk) == $past(d, 2, posedge clk)) |-> (q == $past(q))
    );

    // At each posedge, q equals its value from the most recent negedge (no update occurs at posedge).
    check_q_const_through_posedge: assert property (
        @(posedge clk) q == $past(q, 1, negedge clk)
    );
endmodule