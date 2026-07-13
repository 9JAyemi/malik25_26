module dff_with_reset_and_or_sva (
    input logic clk,
    input logic reset,            // Asynchronous, active-high
    input logic [7:0] d,
    input logic [7:0] q,
    input logic or_out
);
    ///// Reset behavior /////
    // While reset is asserted, q and or_out must be 0.
    reset_forces_outputs_zero: assert property (
        @(negedge clk) reset |-> (q == 8'b0) && (or_out == 1'b0)
    );

    // If reset remains asserted across consecutive cycles, outputs stay at 0.
    hold_zero_while_reset_held: assert property (
        @(negedge clk) ($past(reset) && reset) |-> (q == 8'b0) && (or_out == 1'b0)
    );

    // If reset remains asserted across consecutive cycles, outputs are stable.
    stable_during_reset: assert property (
        @(negedge clk) ($past(reset) && reset) |-> $stable(q) && $stable(or_out)
    );

    // On the first cycle after reset deasserts, or_out must be 0 (prior q was 0).
    or_out_zero_after_reset_release: assert property (
        @(negedge clk) ($past(reset) && !reset) |-> (or_out == 1'b0)
    );

    ///// Sequential capture rules /////
    // q captures d on each negedge (checked as one-cycle-late due to SVA sampling).
    q_captures_d: assert property (
        @(negedge clk) disable iff (reset) !$past(reset) |-> (q == $past(d))
    );

    // or_out equals the OR-reduction of q from the previous cycle.
    or_out_matches_prev_q_or: assert property (
        @(negedge clk) disable iff (reset) !$past(reset) |-> (or_out == (|$past(q)))
    );

    ///// Edge-directed implications /////
    // A rising or_out implies at least one bit of previous q was 1.
    or_out_rise_implies_prev_q_nonzero: assert property (
        @(negedge clk) disable iff (reset) $rose(or_out) |-> (|$past(q))
    );

    // A falling or_out implies previous q was all zeros.
    or_out_fall_implies_prev_q_zero: assert property (
        @(negedge clk) disable iff (reset) $fell(or_out) |-> (~|$past(q))
    );

    // If previous q had any 1s, or_out must be 1 this cycle.
    or_out_one_if_prev_q_nonzero: assert property (
        @(negedge clk) disable iff (reset) (|$past(q)) |-> (or_out == 1'b1)
    );

    // If previous q was all zeros, or_out must be 0 this cycle.
    or_out_zero_if_prev_q_zero: assert property (
        @(negedge clk) disable iff (reset) (~|$past(q)) |-> (or_out == 1'b0)
    );
endmodule