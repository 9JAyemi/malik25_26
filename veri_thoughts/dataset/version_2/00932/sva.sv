module top_module_sva (
    input logic clk,
    input logic reset,            // Asynchronous active-LOW reset
    input logic [7:0] d,
    input logic [7:0] q
);
    // Reset LOW forces q to 0 at this clock edge.
    check_reset_low_clears_q: assert property (
        @(posedge clk) (reset == 1'b0) |-> (q == 8'b0)
    );

    // Falling edge of reset sampled at clk also requires q to be 0.
    check_reset_fall_clears_q: assert property (
        @(posedge clk) $fell(reset) |-> (q == 8'b0)
    );

    // If reset is LOW now, q is still 0 on the next clock.
    check_next_cycle_zero_while_reset_low: assert property (
        @(posedge clk) (reset == 1'b0) |=> (q == 8'b0)
    );

    // If reset was LOW on the previous clock, q is 0 now.
    check_prev_reset_low_implies_q_zero_now: assert property (
        @(posedge clk) ($past(reset) == 1'b0) |-> (q == 8'b0)
    );

    // Rising edge of reset sampled at clk keeps q at 0 on this edge.
    check_reset_rise_holds_zero_now: assert property (
        @(posedge clk) $rose(reset) |-> (q == 8'b0)
    );

    // If q is non-zero at a clock edge, reset must be HIGH at that edge.
    check_nonzero_q_implies_reset_high: assert property (
        @(posedge clk) (q != 8'b0) |-> (reset == 1'b1)
    );

    // While reset is LOW across consecutive clocks, q remains stable (zero).
    check_q_stable_across_low_reset: assert property (
        @(posedge clk) (reset == 1'b0 && $past(reset) == 1'b0) |-> $stable(q)
    );
endmodule