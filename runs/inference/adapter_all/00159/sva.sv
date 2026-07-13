module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [3:0] q
);
    // Clock: clk (posedge). Reset: reset (async, active-high). Logic: sequential counter with wrap at 15.

    // Reset drives q to 0 on the next clock.
    reset_clears_q_next: assert property (
        @(posedge clk) reset |=> (q == 4'b0000)
    );

    // While reset is held high across consecutive clocks, q remains 0.
    reset_held_keeps_q_zero: assert property (
        @(posedge clk) (reset && $past(reset)) |-> (q == 4'b0000)
    );

    // When not in reset and q is not 15, q increments by 1 on the next clock.
    increment_when_not_max: assert property (
        @(posedge clk) disable iff (reset) (q != 4'hF) |=> (q == $past(q) + 4'd1)
    );

    // When not in reset and q is 15, q wraps to 0 on the next clock.
    wrap_when_max: assert property (
        @(posedge clk) disable iff (reset) (q == 4'hF) |=> (q == 4'h0)
    );

    // On reset deassertion, q is 0 on that clock.
    q_zero_on_reset_fall: assert property (
        @(posedge clk) $fell(reset) |-> (q == 4'h0)
    );

    // If q is 0 while not in reset, the previous value was 15 or reset was asserted.
    zero_implies_prev_max_or_reset: assert property (
        @(posedge clk) disable iff (reset) (q == 4'h0) |-> (($past(q) == 4'hF) || $past(reset))
    );

    // If q is 1 while not in reset, the previous value was 0.
    one_implies_prev_zero: assert property (
        @(posedge clk) disable iff (reset) (q == 4'h1) |-> ($past(q) == 4'h0)
    );

    // If q is 15 while not in reset, the previous value was 14.
    max_implies_prev_fourteen: assert property (
        @(posedge clk) disable iff (reset) (q == 4'hF) |-> ($past(q) == 4'd14)
    );

    // If q is 14 while not in reset, the next value is 15.
    fourteen_implies_next_fifteen: assert property (
        @(posedge clk) disable iff (reset) (q == 4'd14) |=> (q == 4'hF)
    );

    // If q is 13 while not in reset, the next value is 14.
    thirteen_implies_next_fourteen: assert property (
        @(posedge clk) disable iff (reset) (q == 4'd13) |=> (q == 4'd14)
    );

endmodule