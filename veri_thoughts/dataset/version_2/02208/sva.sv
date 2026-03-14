module BinaryCounter_sva (
    input logic clk,
    input logic rst,
    input logic [3:0] count
);
    ///// Reset behavior /////
    // When reset is HIGH at a clock edge, count must be 0.
    reset_forces_zero: assert property (
        @(posedge clk) rst |-> (count == 4'd0)
    );
    // On a sampled rising edge of reset, count is cleared to 0.
    reset_rise_clears_count: assert property (
        @(posedge clk) $rose(rst) |-> (count == 4'd0)
    );
    // While reset stays HIGH across cycles, count remains 0.
    hold_zero_while_reset: assert property (
        @(posedge clk) (rst && $past(rst)) |-> (count == 4'd0)
    );

    ///// Counting behavior (out of reset) /////
    // If not at max in prior cycle, next value increments by 1.
    increment_when_not_max: assert property (
        @(posedge clk) disable iff (rst) (!$past(rst) && ($past(count) != 4'hF)) |-> (count == ($past(count) + 1))
    );
    // If at max (15) in prior cycle, next value wraps to 0.
    wrap_on_max: assert property (
        @(posedge clk) disable iff (rst) (!$past(rst) && ($past(count) == 4'hF)) |-> (count == 4'd0)
    );
    // Out of reset, count changes every cycle.
    change_every_cycle_out_of_reset: assert property (
        @(posedge clk) disable iff (rst) (!$past(rst)) |-> (count != $past(count))
    );
    // Out of reset, a 0 value must come only from a prior 15.
    zero_only_from_wrap_out_of_reset: assert property (
        @(posedge clk) disable iff (rst) (!$past(rst) && (count == 4'd0)) |-> ($past(count) == 4'hF)
    );
    // After 16 cycles with no reset, count returns to its prior value (mod-16).
    period_16_no_reset: assert property (
        @(posedge clk) disable iff (rst) (!rst)[*16] |=> (count == $past(count,16))
    );
endmodule