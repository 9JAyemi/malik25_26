module d_flip_flop_with_reset_sva (
    input logic clk,
    input logic reset,
    input logic d,
    input logic q
);
    // Synchronous reset drives q to 0 on the next clock.
    reset_clears_q_next: assert property (
        @(posedge clk) reset |=> (q == 1'b0)
    );

    // When previous cycle was not in reset, q equals previous d (1-cycle latency).
    q_eq_prev_d_when_prev_not_reset: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset)) |-> (q == $past(d))
    );

    // If q changes, the cause must be prior reset or prior d differing from prior q.
    q_change_requires_prev_reset_or_prev_d_neq_prev_q: assert property (
        @(posedge clk) disable iff (reset) (q != $past(q)) |-> ($past(reset) || ($past(d) != $past(q)))
    );

    // If prior cycle not in reset and prior d matched prior q, q holds its value.
    q_holds_when_prev_d_eq_prev_q: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset) && ($past(d) == $past(q))) |-> (q == $past(q))
    );

    // If prior cycle not in reset and prior d differed from prior q, q changes accordingly.
    q_toggles_when_prev_d_neq_prev_q: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset) && ($past(d) != $past(q))) |-> (q != $past(q))
    );

    // On reset deassertion edge, q is 0 (due to prior reset).
    q_zero_on_reset_fall: assert property (
        @(posedge clk) $fell(reset) |-> (q == 1'b0)
    );
endmodule