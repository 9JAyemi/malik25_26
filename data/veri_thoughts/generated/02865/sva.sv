module counter_4bit_sva (
    input logic clk,
    input logic reset,          // active-low reset
    input logic [3:0] count,
    input logic max_count
);

    // While reset is asserted low, outputs are forced to 0.
    reset_forces_zero: assert property (
        @(posedge clk) (reset == 1'b0) |-> (count == 4'h0) && (max_count == 1'b0)
    );

    // When count is 0xF, next cycle wraps to 0 and pulses max_count.
    wrap_on_max: assert property (
        @(posedge clk) disable iff (reset == 1'b0) (count == 4'hF) |=> (count == 4'h0) && (max_count == 1'b1)
    );

    // When count is not 0xF, next cycle increments and clears max_count.
    increment_when_not_max: assert property (
        @(posedge clk) disable iff (reset == 1'b0) (count != 4'hF) |=> (count == $past(count) + 4'h1) && (max_count == 1'b0)
    );

    // max_count high implies count is zero in the same cycle.
    max_count_only_with_zero_count: assert property (
        @(posedge clk) disable iff (reset == 1'b0) max_count |-> (count == 4'h0)
    );

    // max_count can only be asserted following a 0xF state (out of reset).
    max_count_only_after_wrap: assert property (
        @(posedge clk) disable iff (reset == 1'b0) (max_count && $past(reset)) |-> ($past(count) == 4'hF)
    );

    // max_count is a single-cycle pulse.
    max_count_one_cycle_pulse: assert property (
        @(posedge clk) disable iff (reset == 1'b0) max_count |=> !max_count
    );

    // When count is 0xF, max_count must be 0 in the same cycle.
    max_low_when_count_is_F: assert property (
        @(posedge clk) disable iff (reset == 1'b0) (count == 4'hF) |-> (max_count == 1'b0)
    );

    // Out of reset, seeing count==0 implies the previous count was 0xF.
    zero_count_means_wrapped: assert property (
        @(posedge clk) disable iff (reset == 1'b0) (reset && $past(reset) && (count == 4'h0)) |-> ($past(count) == 4'hF)
    );

    // After a max_count pulse, next cycle count is 1 and max_count clears.
    next_after_maxcount_is_one: assert property (
        @(posedge clk) disable iff (reset == 1'b0) max_count |=> (count == 4'h1) && (max_count == 1'b0)
    );

    // Out of reset, each step follows either wrap-to-zero or increment-by-one rule.
    update_follows_spec: assert property (
        @(posedge clk) disable iff (reset == 1'b0)
            (reset && $past(reset)) |-> (
                ($past(count) == 4'hF) ? ((count == 4'h0) && (max_count == 1'b1))
                                       : ((count == $past(count) + 4'h1) && (max_count == 1'b0))
            )
    );

endmodule