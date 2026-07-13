module decade_counter_sva (
    input logic clk,
    input logic slowena,
    input logic reset,
    input logic [3:0] q
);
    // Clock: clk. Reset: reset (active-high, synchronous). Mixed: seq state, comb q updates.

    // After reset is asserted, q must be 0 on the next clock.
    reset_clears_q_next: assert property (
        @(posedge clk) reset |=> (q == 4'd0)
    );

    // While reset stays asserted across cycles, q must be 0.
    hold_zero_while_reset: assert property (
        @(posedge clk) (reset && $past(reset)) |-> (q == 4'd0)
    );

    // Any change of q must either set it to 0 or increment by 1 (mod 16).
    q_change_is_zero_or_plus1: assert property (
        @(posedge clk) disable iff (reset) $changed(q) |-> ((q == 4'd0) || (q == ($past(q) + 4'd1)))
    );

    // If q increments by 1 this cycle, slowena had to be LOW in the prior cycle.
    increment_implies_prev_slowena_low: assert property (
        @(posedge clk) disable iff (reset) (q == ($past(q) + 4'd1)) |-> ($past(slowena) == 1'b0)
    );

    // q cannot increment by 1 in two consecutive cycles.
    no_back_to_back_increments: assert property (
        @(posedge clk) disable iff (reset) (q == ($past(q) + 4'd1)) |-> ##1 !(q == ($past(q) + 4'd1))
    );

    // If slowena is HIGH this cycle, q must not increment on the next cycle.
    no_increment_when_slowena_high: assert property (
        @(posedge clk) disable iff (reset) slowena |-> ##1 !(q == ($past(q) + 4'd1))
    );

    // If slowena is HIGH for two consecutive cycles, q is stable in the next cycle.
    slowena_high_two_cycles_stabilizes_q: assert property (
        @(posedge clk) disable iff (reset) (slowena && $past(slowena)) |-> ##1 (q == $past(q))
    );

    // A transition from 0 to non-zero must be to 1.
    zero_to_nonzero_becomes_one: assert property (
        @(posedge clk) disable iff (reset) ($past(q) == 4'd0 && q != 4'd0) |-> (q == 4'd1)
    );

    // A falling edge on slowena causes q to increment on the next cycle.
    slowena_fall_causes_increment_next: assert property (
        @(posedge clk) disable iff (reset) ($past(slowena) && !slowena) |-> ##1 (q == ($past(q) + 4'd1))
    );

    // After reset deasserts and slowena is HIGH, q holds its value into the next cycle.
    post_reset_deassert_with_slowena_high_holds_q: assert property (
        @(posedge clk) disable iff (reset) ($past(reset) && !reset && slowena) |-> ##1 (q == $past(q))
    );

endmodule