module counter_4bit_sva (
    input logic clk,
    input logic reset,   // synchronous, active-high
    input logic load,
    input logic [3:0] data,
    input logic [3:0] count
);
    // On reset, next cycle count is zero.
    reset_sets_zero: assert property (
        @(posedge clk) reset |=> (count == 4'd0)
    );

    // Reset has priority over load when both are high.
    reset_overrides_load: assert property (
        @(posedge clk) (reset && load) |=> (count == 4'd0)
    );

    // When load is high (and not in reset), count loads data on the next cycle.
    load_updates_count: assert property (
        @(posedge clk) disable iff (reset) load |=> (count == $past(data))
    );

    // If previous cycle was not reset and not load, and count was not 0xF, it increments by 1.
    increment_no_wrap: assert property (
        @(posedge clk) (!$past(reset) && !$past(load) && ($past(count) != 4'hF)) |-> (count == $past(count) + 4'd1)
    );

    // If previous cycle was not reset and not load, and count was 0xF, it wraps to 0.
    increment_wrap: assert property (
        @(posedge clk) (!$past(reset) && !$past(load) && ($past(count) == 4'hF)) |-> (count == 4'h0)
    );

    // If reset was high in the previous cycle, count is 0 in the current cycle.
    prev_reset_forces_zero: assert property (
        @(posedge clk) $past(reset) |-> (count == 4'd0)
    );

    // With no load in the previous cycle (and not in reset), count must change.
    increment_changes_value: assert property (
        @(posedge clk) (!$past(reset) && !$past(load)) |-> (count != $past(count))
    );
endmodule