module decade_counter_sva (
    input logic clk,
    input logic reset,   // Active-high synchronous reset
    input logic pause,
    input logic [3:0] q
);

    ///// Reset behavior /////
    // On a clock with reset asserted, q must be 0 on the next clock.
    reset_clears_output_next: assert property (
        @(posedge clk) reset |=> (q == 4'd0)
    );

    ///// Output value restrictions /////
    // q can never take the value 10 due to output mapping.
    q_never_ten: assert property (
        @(posedge clk) disable iff (reset) q != 4'd10
    );

    ///// Pause semantics /////
    // While paused, q holds its value to the next clock.
    pause_holds_q: assert property (
        @(posedge clk) disable iff (reset) pause |=> $stable(q)
    );
    // If pause remains asserted for two consecutive clocks, q stays stable.
    pause_two_cycle_hold: assert property (
        @(posedge clk) disable iff (reset) $past(pause) && pause |-> $stable(q)
    );
    // When pause deasserts, q changes on the following clock.
    change_after_pause_deassert: assert property (
        @(posedge clk) disable iff (reset) $fell(pause) |=> (q != $past(q))
    );

    ///// Counting behavior when not paused /////
    // When not paused, q changes every clock (advance or wrap).
    not_pause_always_changes_q: assert property (
        @(posedge clk) disable iff (reset) !pause |=> (q != $past(q))
    );
    // When not paused and q is 1..8, next q increments by +1.
    step_q_1_to_8_inc: assert property (
        @(posedge clk) disable iff (reset) (!pause && (q >= 4'd1) && (q <= 4'd8)) |=> (q == $past(q) + 4'd1)
    );
    // When not paused and q is 11..14, next q increments by +1.
    step_q_11_to_14_inc: assert property (
        @(posedge clk) disable iff (reset) (!pause && (q >= 4'd11) && (q <= 4'd14)) |=> (q == $past(q) + 4'd1)
    );
    // When not paused and q is 9, next q wraps to 0.
    step_q_9_to_0: assert property (
        @(posedge clk) disable iff (reset) (!pause && (q == 4'd9)) |=> (q == 4'd0)
    );
    // When not paused and q is 15, next q wraps to 0 (4-bit rollover).
    step_q_15_to_0: assert property (
        @(posedge clk) disable iff (reset) (!pause && (q == 4'd15)) |=> (q == 4'd0)
    );

endmodule