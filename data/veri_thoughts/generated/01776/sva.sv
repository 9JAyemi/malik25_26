module binary_counter_sva (
    input logic clk,
    input logic reset,
    input logic enable,
    input logic load,
    input logic [3:0] in,
    input logic [3:0] out,
    input logic overflow
);
    // overflow reflects out == 4'hF.
    check_overflow_definition: assert property (
        @(posedge clk) disable iff (reset) overflow == (out == 4'hF)
    );

    // After a reset cycle, out is 0 on the next cycle.
    check_sync_reset_clears_out: assert property (
        @(posedge clk) disable iff (reset) $past(reset) |-> (out == 4'h0)
    );

    // Load updates out with in on the next cycle.
    check_load_updates_out: assert property (
        @(posedge clk) disable iff (reset) ($past(load) && !$past(reset)) |-> (out == $past(in))
    );

    // Enable increments out by 1 when not wrapping (no load).
    check_enable_increments_no_wrap: assert property (
        @(posedge clk) disable iff (reset)
            ($past(enable) && !$past(load) && !$past(reset) && ($past(out) != 4'hF))
            |-> (out == ($past(out) + 4'd1))
    );

    // Enable wraps from 4'hF to 4'h0 (no load).
    check_enable_wraps_from_max: assert property (
        @(posedge clk) disable iff (reset)
            ($past(enable) && !$past(load) && !$past(reset) && ($past(out) == 4'hF))
            |-> (out == 4'h0)
    );

    // Hold value when neither load nor enable are asserted.
    check_hold_when_idle: assert property (
        @(posedge clk) disable iff (reset)
            (!$past(reset) && !$past(load) && !$past(enable))
            |-> (out == $past(out))
    );

    // Load has priority over enable when both are asserted.
    check_load_has_priority_over_enable: assert property (
        @(posedge clk) disable iff (reset)
            ($past(load) && $past(enable) && !$past(reset))
            |-> (out == $past(in))
    );

    // Any change in out must be caused by reset, load, or enable in the previous cycle.
    check_change_has_known_cause: assert property (
        @(posedge clk) disable iff (reset)
            (out != $past(out)) |-> ($past(reset) || $past(load) || $past(enable))
    );

    // Overflow can only rise when out reaches 4'hF.
    check_overflow_rise_on_out_max: assert property (
        @(posedge clk) disable iff (reset)
            $rose(overflow) |-> (out == 4'hF) && ($past(out) != 4'hF)
    );

    // Overflow can only fall when leaving 4'hF.
    check_overflow_fall_on_out_below_max: assert property (
        @(posedge clk) disable iff (reset)
            $fell(overflow) |-> ($past(out) == 4'hF) && (out != 4'hF)
    );
endmodule