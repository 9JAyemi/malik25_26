module FFType_sva (
    input logic clock,
    input logic reset,      // active-high synchronous reset
    input logic io_in,
    input logic io_init,
    input logic io_out,
    input logic io_enable
);
    // On reset, output equals init value that cycle.
    check_reset_assigns_init: assert property (
        @(posedge clock) reset |-> (io_out == io_init)
    );

    // When enabled (and not in reset), output equals input that cycle.
    check_enable_updates_out: assert property (
        @(posedge clock) disable iff (reset) io_enable |-> (io_out == io_in)
    );

    // Output changes only when reset or enable is asserted in this cycle.
    check_change_requires_update: assert property (
        @(posedge clock) $changed(io_out) |-> (reset || io_enable)
    );

    // If disabled in two consecutive non-reset cycles, output holds its value.
    check_hold_two_cycles_no_enable: assert property (
        @(posedge clock) disable iff (reset) (!io_enable && $past(!io_enable) && !$past(reset)) |-> (io_out == $past(io_out))
    );

    // If previous cycle was enable (no reset) and now disabled, output equals prior input.
    check_prev_enable_capture_when_now_disabled: assert property (
        @(posedge clock) disable iff (reset) ($past(io_enable) && !$past(reset) && !io_enable) |-> (io_out == $past(io_in))
    );

    // If previous cycle was reset and now not enabling, output equals prior init.
    check_prev_reset_capture_when_now_disabled: assert property (
        @(posedge clock) disable iff (reset) ($past(reset) && !io_enable) |-> (io_out == $past(io_init))
    );

    // Reset has priority over enable when both are asserted.
    check_reset_priority_over_enable: assert property (
        @(posedge clock) (reset && io_enable) |-> (io_out == io_init)
    );

    // While disabled (not in reset), output does not change in that cycle.
    check_stable_when_disabled: assert property (
        @(posedge clock) disable iff (reset) (!io_enable) |-> $stable(io_out)
    );
endmodule