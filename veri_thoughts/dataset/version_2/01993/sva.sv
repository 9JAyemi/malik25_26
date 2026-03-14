module kb_code_sva (
    input logic clk,
    input logic reset,
    input logic scan_done_tick,
    input logic [7:0] scan_out,
    input logic got_code_tick
);
    localparam logic [7:0] BRK = 8'hf0;

    // While reset is asserted, output tick must be LOW.
    reset_clears_tick: assert property (
        @(posedge clk) reset |-> (got_code_tick == 1'b0)
    );

    // No tick when scan_done_tick is LOW.
    tick_requires_done: assert property (
        @(posedge clk) disable iff (reset) (scan_done_tick == 1'b0) |-> (got_code_tick == 1'b0)
    );

    // got_code_tick is a single-cycle pulse.
    tick_one_cycle_pulse: assert property (
        @(posedge clk) disable iff (reset) got_code_tick |=> !got_code_tick
    );

    // After a tick, remain LOW until a BRK code is observed with scan_done_tick.
    holdoff_until_break_after_tick: assert property (
        @(posedge clk) disable iff (reset) got_code_tick |=> (!got_code_tick until (scan_done_tick && (scan_out == BRK)))
    );

    // If previous cycle was BRK with done and no tick, then current done must raise tick.
    break_then_next_done_yields_tick: assert property (
        @(posedge clk) disable iff (reset)
            $past(!reset) && $past(scan_done_tick && (scan_out == BRK) && !got_code_tick) && scan_done_tick |-> got_code_tick
    );

    // With back-to-back done pulses, if prior was not BRK in wait_brk, then no tick now.
    consecutive_done_without_break_no_tick: assert property (
        @(posedge clk) disable iff (reset)
            scan_done_tick && $past(!reset) && $past(scan_done_tick) && !($past(scan_out == BRK) && !$past(got_code_tick)) |-> !got_code_tick
    );

    // With back-to-back done pulses, a tick now implies prior was BRK and no tick.
    consecutive_done_tick_implies_prev_break: assert property (
        @(posedge clk) disable iff (reset)
            scan_done_tick && $past(!reset) && $past(scan_done_tick) && got_code_tick |-> $past(scan_out == BRK) && !$past(got_code_tick)
    );

    // After reset deasserts, no tick until a BRK code is seen with scan_done_tick.
    after_reset_block_tick_until_break: assert property (
        @(posedge clk) $fell(reset) |-> (!got_code_tick until (scan_done_tick && (scan_out == BRK)))
    );

    // On the first cycle after reset deasserts, a BRK done does not raise tick.
    first_cycle_after_reset_break_no_tick: assert property (
        @(posedge clk) $past(reset) && !reset && scan_done_tick && (scan_out == BRK) |-> !got_code_tick
    );
endmodule