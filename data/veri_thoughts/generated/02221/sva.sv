module counter_sva (
    input logic clk,
    input logic reset,
    input logic [3:0] i_value,
    input logic [3:0] value
);
    // On any clock after reset is high, value must be 0.
    reset_clears_next: assert property (
        @(posedge clk) reset |=> (value == 4'h0)
    );

    // If reset stays asserted across consecutive clocks, value stays 0.
    reset_holds_zero: assert property (
        @(posedge clk) ($past(reset) && reset) |-> (value == 4'h0)
    );

    // When not in reset previously and value was not 0xF, increment by 1.
    inc_when_not_max: assert property (
        @(posedge clk) disable iff (reset) $past(!reset) && ($past(value) != 4'hF) |-> (value == ($past(value) + 4'h1))
    );

    // When not in reset previously and value was 0xF, wrap to 0.
    wrap_when_max: assert property (
        @(posedge clk) disable iff (reset) $past(!reset) && ($past(value) == 4'hF) |-> (value == 4'h0)
    );

    // Out of reset, value must change every cycle (increment or wrap).
    change_each_cycle_out_of_reset: assert property (
        @(posedge clk) disable iff (reset) $past(!reset) |-> (value != $past(value))
    );

    // Sanity: value is always within 4-bit range.
    value_within_range: assert property (
        @(posedge clk) 1'b1 |-> (value inside {[4'h0:4'hF]})
    );
endmodule