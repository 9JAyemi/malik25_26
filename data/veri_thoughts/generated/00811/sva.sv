module jk_flip_flop_sva (
    input logic clk,
    input logic clr_n,
    input logic j,
    input logic k,
    input logic q,
    input logic q_n
);
    ///// Basic reset and inversion rules /////
    // When reset is asserted (active low), q must be 0 and q_n must be 1.
    check_reset_forces_outputs: assert property (
        @(negedge clk) (!clr_n) |-> (q == 1'b0) && (q_n == 1'b1)
    );
    // q_n is always the logical inverse of q when not in reset.
    check_qn_complement_nonreset_negedge: assert property (
        @(negedge clk) disable iff (!clr_n) (q_n == ~q)
    );
    // q_n is always the logical inverse of q on the rising edge as well (not in reset).
    check_qn_complement_nonreset_posedge: assert property (
        @(posedge clk) disable iff (!clr_n) (q_n == ~q)
    );
    // q_n remains the logical inverse of q even during reset.
    check_qn_complement_during_reset: assert property (
        @(negedge clk) (!clr_n) |-> (q_n == ~q)
    );

    ///// Asynchronous reset dominance across edges /////
    // If the previous edge was in reset, q must be 0 at this edge (before state update).
    check_q_zero_after_prev_reset: assert property (
        @(negedge clk) disable iff (!clr_n) $past(!clr_n) |-> (q == 1'b0)
    );

    ///// JK next-state behavior sampled on negedge /////
    // If previous edge had J=0,K=0 (and was not in reset), q holds its value.
    check_jk_hold_on_00: assert property (
        @(negedge clk) disable iff (!clr_n)
            $past(clr_n) && ($past(j) == 1'b0) && ($past(k) == 1'b0) |-> (q == $past(q))
    );
    // If previous edge had J=0,K=1 (and was not in reset), q goes to 0.
    check_jk_reset_on_01: assert property (
        @(negedge clk) disable iff (!clr_n)
            $past(clr_n) && ($past(j) == 1'b0) && ($past(k) == 1'b1) |-> (q == 1'b0)
    );
    // If previous edge had J=1,K=0 (and was not in reset), q goes to 1.
    check_jk_set_on_10: assert property (
        @(negedge clk) disable iff (!clr_n)
            $past(clr_n) && ($past(j) == 1'b1) && ($past(k) == 1'b0) |-> (q == 1'b1)
    );
    // If previous edge had J=1,K=1 (and was not in reset), q toggles.
    check_jk_toggle_on_11: assert property (
        @(negedge clk) disable iff (!clr_n)
            $past(clr_n) && ($past(j) == 1'b1) && ($past(k) == 1'b1) |-> (q == ~$past(q))
    );
    // Two consecutive toggle commands (with no resets on those edges) restore q to its original value.
    check_double_toggle_restores: assert property (
        @(negedge clk) disable iff (!clr_n)
            $past(clr_n,2) && $past(clr_n,1) &&
            ($past(j,2) == 1'b1) && ($past(k,2) == 1'b1) &&
            ($past(j,1) == 1'b1) && ($past(k,1) == 1'b1) |-> (q == $past(q,2))
    );
endmodule