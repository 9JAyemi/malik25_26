module sync_counter_sva (
    input logic clk,
    input logic reset,
    input logic count_en,
    input logic load,
    input logic [3:0] data_in,
    input logic [3:0] count_val,
    input logic overflow,
    input logic underflow
);
    // Clock: clk; Reset: reset (active-high, synchronous). All logic is sequential on posedge clk.

    // On reset, next cycle outputs are cleared.
    check_reset_clears_next: assert property (
        @(posedge clk) reset |=> (count_val == 4'b0000) && (overflow == 1'b0) && (underflow == 1'b0)
    );

    // Load has priority and updates count_val; flags clear next cycle.
    check_load_updates_and_clears_flags: assert property (
        @(posedge clk) disable iff (reset) load |=> (count_val == $past(data_in)) && (overflow == 1'b0) && (underflow == 1'b0)
    );

    // When counting up at max (0xF), wrap to 0 and set overflow; underflow clears.
    check_countup_wrap_sets_overflow: assert property (
        @(posedge clk) disable iff (reset) (!load && count_en && (count_val == 4'hF)) |=> (count_val == 4'h0) && (overflow == 1'b1) && (underflow == 1'b0)
    );

    // When counting up below max, increment by 1; both flags clear.
    check_countup_increment_clears_flags: assert property (
        @(posedge clk) disable iff (reset) (!load && count_en && (count_val != 4'hF)) |=> (count_val == ($past(count_val) + 4'd1)) && (overflow == 1'b0) && (underflow == 1'b0)
    );

    // When counting down at 0, wrap to 0xF and set underflow; overflow clears.
    check_countdown_wrap_sets_underflow: assert property (
        @(posedge clk) disable iff (reset) (!load && !count_en && (count_val == 4'h0)) |=> (count_val == 4'hF) && (underflow == 1'b1) && (overflow == 1'b0)
    );

    // When counting down above 0, decrement by 1; both flags clear.
    check_countdown_decrement_clears_flags: assert property (
        @(posedge clk) disable iff (reset) (!load && !count_en && (count_val != 4'h0)) |=> (count_val == ($past(count_val) - 4'd1)) && (overflow == 1'b0) && (underflow == 1'b0)
    );

    // Overflow and underflow are never asserted simultaneously.
    check_flags_mutex: assert property (
        @(posedge clk) disable iff (reset) !(overflow && underflow)
    );

    // On any countdown step (load=0, count_en=0), overflow is 0 next cycle.
    check_no_overflow_on_countdown: assert property (
        @(posedge clk) disable iff (reset) (!load && !count_en) |=> (overflow == 1'b0)
    );

    // On any count-up step (load=0, count_en=1), underflow is 0 next cycle.
    check_no_underflow_on_countup: assert property (
        @(posedge clk) disable iff (reset) (!load && count_en) |=> (underflow == 1'b0)
    );

    // Without load, the counter value always changes next cycle.
    check_no_hold_without_load: assert property (
        @(posedge clk) disable iff (reset) (!load) |=> (count_val != $past(count_val))
    );

    // Overflow cannot occur in two consecutive cycles.
    check_no_back_to_back_overflow: assert property (
        @(posedge clk) disable iff (reset) overflow |=> (overflow == 1'b0)
    );

    // Underflow cannot occur in two consecutive cycles.
    check_no_back_to_back_underflow: assert property (
        @(posedge clk) disable iff (reset) underflow |=> (underflow == 1'b0)
    );

endmodule