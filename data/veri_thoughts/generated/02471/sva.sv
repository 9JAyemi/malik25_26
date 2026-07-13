module up_counter_sva (
    input logic clk,
    input logic reset,
    input logic [2:0] out
);
    // Clock: clk; Reset: reset (active-high synchronous). Sequential 3-bit up-counter.

    // On a clock when reset is HIGH, out becomes zero on the next clock.
    reset_clears_next: assert property (
        @(posedge clk) reset |=> (out == 3'd0)
    );

    // If the previous cycle had reset HIGH, out must be zero now.
    post_reset_out_zero: assert property (
        @(posedge clk) $past(reset) |-> (out == 3'd0)
    );

    // With no reset in the current and previous cycle, out increments by 1 modulo 8.
    inc_by_one_no_reset: assert property (
        @(posedge clk) disable iff (reset)
            (!$past(reset)) |-> (out == ($past(out) + 3'd1)[2:0])
    );

    // When previous out was 7 and no reset in the previous cycle, wrap to 0.
    wrap_from_7_to_0: assert property (
        @(posedge clk) disable iff (reset)
            (!$past(reset) && ($past(out) == 3'd7)) |-> (out == 3'd0)
    );

    // Over two consecutive non-reset cycles, out advances by 2 modulo 8.
    inc_by_two_over_two_cycles: assert property (
        @(posedge clk) disable iff (reset)
            (!$past(reset) && !$past(reset,2)) |-> (out == ($past(out,2) + 3'd2)[2:0])
    );

    // Over eight consecutive non-reset cycles, out returns to the same value (period 8).
    periodicity_over_8_cycles: assert property (
        @(posedge clk) disable iff (reset)
            (!$past(reset,1) && !$past(reset,2) && !$past(reset,3) && !$past(reset,4) &&
             !$past(reset,5) && !$past(reset,6) && !$past(reset,7) && !$past(reset,8)) |-> (out == $past(out,8))
    );

    // With no reset in current and previous cycle, out must change every cycle.
    must_change_each_nonreset_cycle: assert property (
        @(posedge clk) disable iff (reset)
            (!$past(reset)) |-> (out != $past(out))
    );

endmodule