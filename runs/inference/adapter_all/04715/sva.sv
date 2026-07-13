module counter_4bit_sva (
    input logic clk,
    input logic reset,
    input logic enable,
    input logic [3:0] count
);
    // Clock: clk (posedge). Reset: reset (synchronous, active-high). Sequential 4-bit counter with enable.

    // Reset drives count to zero on the next cycle.
    reset_clears_count_next: assert property (
        @(posedge clk) reset |=> (count == 4'b0000)
    );

    // When enabled without reset, count increments by 1 on the next cycle.
    increment_when_enabled: assert property (
        @(posedge clk) disable iff (reset) enable |=> (count == $past(count) + 4'd1)
    );

    // When not enabled without reset, count holds its value on the next cycle.
    hold_when_disabled: assert property (
        @(posedge clk) disable iff (reset) !enable |=> (count == $past(count))
    );

    // Wrap from 15 to 0 when enabled without reset.
    wrap_from_max: assert property (
        @(posedge clk) disable iff (reset) (enable && (count == 4'hF)) |=> (count == 4'h0)
    );

    // Any change in count (without reset) implies enable was high in the prior cycle.
    change_requires_enable: assert property (
        @(posedge clk) disable iff (reset) (count != $past(count)) |-> $past(enable)
    );

    // With reset held high across cycles, count remains zero.
    reset_hold_keeps_zero: assert property (
        @(posedge clk) (reset && $past(reset)) |-> (count == 4'h0)
    );

    // With reset held high across cycles, any change in count must be due to enable.
    reset_hold_change_requires_enable: assert property (
        @(posedge clk) (reset && $past(reset) && (count != $past(count))) |-> $past(enable)
    );

    // With reset held high across cycles, count cannot increment by more than 1 per cycle.
    reset_hold_increment_bound: assert property (
        @(posedge clk) (reset && $past(reset) && (count != $past(count))) |-> (count <= $past(count) + 4'd1)
    );

    // With reset held high across cycles, count cannot decrement.
    reset_hold_no_decrement: assert property (
        @(posedge clk) (reset && $past(reset) && (count != $past(count))) |-> (count >= $past(count))
    );

    // With reset held high across cycles, count cannot hold its value.
    reset_hold_no_hold: assert property (
        @(posedge clk) (reset && $past(reset) && (count == $past(count))) |-> 1'b0
    );

endmodule