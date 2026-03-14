module uart_baud_clk_sva (
    input logic clk,
    input logic reset,
    input logic baud_clk_tick,
    input logic [15:0] q_cnt,
    input logic [15:0] d_cnt
);
    // On reset, counter must be 0.
    check_reset_clears_counter: assert property (
        @(posedge clk) reset |-> (q_cnt == 16'h0000)
    );

    // While reset is held, counter stays 0 into the next cycle.
    check_reset_holds_zero: assert property (
        @(posedge clk) reset |=> (q_cnt == 16'h0000)
    );

    // q_cnt updates from previous cycle's d_cnt (when not in reset).
    check_q_cnt_follows_d_cnt: assert property (
        @(posedge clk) disable iff (reset) 1'b1 |=> (q_cnt == $past(d_cnt))
    );

    // If previous cycle had a tick, q_cnt wraps to 0 this cycle.
    check_next_on_prev_tick: assert property (
        @(posedge clk) disable iff (reset) ($past(baud_clk_tick) && !$past(reset)) |-> (q_cnt == 16'h0000)
    );

    // If previous cycle had no tick, q_cnt increments by 1 this cycle.
    check_next_on_prev_no_tick: assert property (
        @(posedge clk) disable iff (reset) (!$past(baud_clk_tick) && !$past(reset)) |-> (q_cnt == ($past(q_cnt) + 16'h0001))
    );

    // After any non-reset cycle, q_cnt is either 0 or previous+1.
    check_monotonic_or_wrap: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset)) |-> ((q_cnt == 16'h0000) || (q_cnt == ($past(q_cnt) + 16'h0001)))
    );

    // d_cnt equals 0 when tick is 1, else it equals q_cnt+1 (combinational definition).
    check_d_cnt_matches_tick_logic: assert property (
        @(posedge clk) disable iff (reset) d_cnt == (baud_clk_tick ? 16'h0000 : (q_cnt + 16'h0001))
    );

    // Tick pulses are single-cycle: next cycle must be LOW.
    check_tick_single_cycle_next_low: assert property (
        @(posedge clk) disable iff (reset) baud_clk_tick |=> !baud_clk_tick
    );

    // No back-to-back tick HIGHs: previous cycle must be LOW.
    check_tick_not_back_to_back_prev_low: assert property (
        @(posedge clk) disable iff (reset) baud_clk_tick |-> !$past(baud_clk_tick)
    );

    // A tick this cycle forces next q_cnt to 0.
    check_tick_implies_next_cnt_zero: assert property (
        @(posedge clk) disable iff (reset) baud_clk_tick |=> (q_cnt == 16'h0000)
    );
endmodule