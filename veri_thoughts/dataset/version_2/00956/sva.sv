module dff_pipeline_sva (
    input logic clk,
    input logic clr,   // active-LOW asynchronous clear
    input logic d,
    input logic q
);

    ///// Reset behavior /////
    // While reset is asserted (clr==0), q must be HIGH.
    reset_forces_q_high: assert property (
        @(posedge clk) !clr |-> (q == 1'b1)
    );

    // If reset remains asserted across consecutive cycles, q stays HIGH.
    reset_hold_q_stable: assert property (
        @(posedge clk) ($past(clr) == 1'b0 && clr == 1'b0) |-> (q == 1'b1 && $stable(q))
    );

    // On a falling edge of clr, q must be HIGH in the same sampled cycle.
    q_high_on_reset_fall: assert property (
        @(posedge clk) $fell(clr) |-> (q == 1'b1)
    );

    // On a rising edge of clr (reset release), q was HIGH in the previous cycle.
    q_prev_high_on_reset_release: assert property (
        @(posedge clk) $rose(clr) |-> ($past(q) == 1'b1)
    );

    // q can be 0 only when not in reset.
    q_zero_only_out_of_reset: assert property (
        @(posedge clk) (q == 1'b0) |-> (clr == 1'b1)
    );

    // Changes on d during held reset must not affect q (q stays HIGH).
    d_changes_ignored_during_reset: assert property (
        @(posedge clk) ($past(clr) == 1'b0 && clr == 1'b0 && $changed(d)) |-> (q == 1'b1 && $stable(q))
    );

    ///// Functional behavior under no reset /////
    // With clr HIGH for the last 3 cycles, q equals d from 3 cycles ago (3-stage pipeline).
    pipeline_3cycle_delay_when_not_reset: assert property (
        @(posedge clk) disable iff (!clr)
            (clr && $past(clr) && $past(clr,2) && $past(clr,3)) |-> (q == $past(d,3))
    );

endmodule