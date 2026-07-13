module top_module_sva (
    input logic clk,
    input logic d,
    input logic q,
    // Internal wires from top_module
    input logic q_ff1,
    input logic q_ff2
);
    ///// Structural/connectivity /////
    // q must always equal q_ff2 (continuous assign).
    check_q_equals_q_ff2: assert property (
        @(posedge clk) q === q_ff2
    );

    ///// Stability on posedge (outputs only update on negedge) /////
    // q_ff1 does not change on posedge.
    check_qff1_stable_on_posedge: assert property (
        @(posedge clk) $past(1'b1) |-> $stable(q_ff1)
    );
    // q_ff2 does not change on posedge.
    check_qff2_stable_on_posedge: assert property (
        @(posedge clk) $past(1'b1) |-> $stable(q_ff2)
    );
    // q does not change on posedge.
    check_q_stable_on_posedge: assert property (
        @(posedge clk) $past(1'b1) |-> $stable(q)
    );

    ///// Dual-edge flip-flop behavior /////
    // ff1: On each negedge, q_ff1 equals d sampled at the preceding posedge.
    check_ff1_negedge_samples_prior_posedge_d: assert property (
        @(negedge clk) $past(1'b1, 1, posedge clk) |-> (q_ff1 == $past(d, 1, posedge clk))
    );
    // ff2: On each negedge, q (q_ff2) equals q_ff1 sampled at the preceding posedge.
    check_ff2_negedge_samples_prior_posedge_qff1: assert property (
        @(negedge clk) $past(1'b1, 1, posedge clk) |-> (q == $past(q_ff1, 1, posedge clk))
    );
    // Top-level pipeline: On each negedge, q equals d from two posedges earlier.
    check_top_negedge_matches_d_two_posedges_ago: assert property (
        @(negedge clk) $past(1'b1, 2, posedge clk) |-> (q == $past(d, 2, posedge clk))
    );
endmodule