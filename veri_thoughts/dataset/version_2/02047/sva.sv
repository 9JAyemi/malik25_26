module freq_divider_sva (
    input logic clk,
    input logic reset,
    input logic out_clk
);
    ///// Reset behavior /////
    // While reset is asserted low, out_clk must be 0.
    reset_low_out_zero: assert property (
        @(posedge clk) (!reset) |-> (out_clk == 1'b0)
    );

    // On the cycle where reset falls (asynchronous assert), out_clk must be 0.
    async_reset_fall_clears_out: assert property (
        @(posedge clk) $fell(reset) |-> (out_clk == 1'b0)
    );

    // On the first clock after reset deasserts high, out_clk remains 0.
    out_zero_on_first_cycle_after_deassert: assert property (
        @(posedge clk) disable iff (!reset) $rose(reset) |-> (out_clk == 1'b0)
    );

    // On the second clock after reset deasserts high, out_clk becomes 1.
    out_one_on_second_cycle_after_deassert: assert property (
        @(posedge clk) disable iff (!reset) $rose(reset) |-> ##1 (out_clk == 1'b1)
    );

    ///// Divide-by-2 behavior /////
    // After at least one active cycle, out_clk toggles every clock.
    toggle_every_cycle_after_warmup: assert property (
        @(posedge clk) disable iff (!reset) $past(reset) |-> (out_clk != $past(out_clk))
    );

    // After at least two active cycles, out_clk repeats its value every two clocks.
    periodicity_two_cycles: assert property (
        @(posedge clk) disable iff (!reset) $past(reset,2) |-> (out_clk == $past(out_clk,2))
    );

    // Any rising edge of out_clk is followed by a falling edge next cycle.
    rise_followed_by_fall: assert property (
        @(posedge clk) disable iff (!reset) $rose(out_clk) |-> ##1 $fell(out_clk)
    );

    // Any falling edge of out_clk is followed by a rising edge next cycle.
    fall_followed_by_rise: assert property (
        @(posedge clk) disable iff (!reset) $fell(out_clk) |-> ##1 $rose(out_clk)
    );
endmodule