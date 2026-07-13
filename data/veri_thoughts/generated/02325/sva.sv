module d_ff_sync_rst_sva (
    input logic clk,
    input logic rst,
    input logic d,
    input logic q
);
    // Clock: clk; Reset: rst (active-high, synchronous). Sequential D-FF with sync reset.

    // Q matches previous cycle's (rst ? 0 : d).
    check_next_state_from_prev_inputs: assert property (
        @(posedge clk) $past(1'b1) |-> (q == ($past(rst) ? 1'b0 : $past(d)))
    );

    // If reset was 1 in the previous cycle, Q is 0 now.
    check_q_zero_after_prev_reset: assert property (
        @(posedge clk) $past(rst) |-> (q == 1'b0)
    );

    // If reset was 0 in the previous cycle, Q equals previous D.
    check_q_follows_prev_d_when_no_reset: assert property (
        @(posedge clk) !$past(rst) |-> (q == $past(d))
    );

    // When not in reset previously and D matched prior Q, Q holds its value.
    check_hold_when_input_matches: assert property (
        @(posedge clk) disable iff (rst) ($past(1'b1) && !$past(rst) && ($past(d) == $past(q))) |-> (q == $past(q))
    );

    // When not in reset previously and D differed from prior Q, Q updates to prior D and changes.
    check_update_when_input_differs: assert property (
        @(posedge clk) disable iff (rst) ($past(1'b1) && !$past(rst) && ($past(d) != $past(q))) |-> ((q == $past(d)) && (q != $past(q)))
    );

    // While reset is held across consecutive cycles, Q is 0.
    check_q_zero_while_reset_held: assert property (
        @(posedge clk) ($past(rst) && rst) |-> (q == 1'b0)
    );

    // On the cycle reset deasserts (was 1, now 0), Q remains 0 from the prior reset assignment.
    check_q_zero_on_reset_release: assert property (
        @(posedge clk) ($past(rst) && !rst) |-> (q == 1'b0)
    );

endmodule