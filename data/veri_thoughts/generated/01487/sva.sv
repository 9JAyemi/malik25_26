module counter_sva #(
    parameter WIDTH = 8,
    parameter MODULUS = 256
)(
    input logic clk,
    input logic ce,
    input logic clr,
    input logic [WIDTH-1:0] out
);
    ///// Clock: clk; Reset: clr (synchronous, active-high) /////

    // After any cycle with clr HIGH, out must be 0 on the next cycle.
    check_sync_clear_next_zero: assert property (
        @(posedge clk) disable iff (clr) $past(clr) |-> (out == '0)
    );

    // With no clr and ce LOW in the previous cycle, out holds its value.
    check_hold_without_ce: assert property (
        @(posedge clk) disable iff (clr) (!$past(clr) && !$past(ce)) |-> (out == $past(out))
    );

    // With no clr and ce HIGH below MODULUS-1 in the previous cycle, out increments by 1.
    check_increment_when_ce_high_below_max: assert property (
        @(posedge clk) disable iff (clr)
        (!$past(clr) && $past(ce) && ($past(out) != MODULUS-1)) |-> (out == $past(out) + 1)
    );

    // With no clr and ce HIGH at MODULUS-1 in the previous cycle, out wraps to 0.
    check_wrap_when_ce_high_at_max: assert property (
        @(posedge clk) disable iff (clr)
        (!$past(clr) && $past(ce) && ($past(out) == MODULUS-1)) |-> (out == '0)
    );

    // Any change in out must be caused by prior clr or ce.
    check_change_requires_ce_or_clr_prev: assert property (
        @(posedge clk) disable iff (clr) (out != $past(out)) |-> ($past(clr) || $past(ce))
    );

    // A transition to 0 (from non-zero) without prior clr must be a wrap from MODULUS-1 with ce.
    check_zero_transition_only_on_wrap_or_reset: assert property (
        @(posedge clk) disable iff (clr)
        (!$past(clr) && (out == '0) && ($past(out) != '0)) |-> ($past(ce) && ($past(out) == MODULUS-1))
    );

    // With prior ce and no prior clr, the next state is either increment or wrap (no other values).
    check_ce_step_is_inc_or_wrap: assert property (
        @(posedge clk) disable iff (clr)
        (!$past(clr) && $past(ce)) |-> (
            (($past(out) == MODULUS-1) && (out == '0)) ||
            (($past(out) != MODULUS-1) && (out == $past(out) + 1))
        )
    );

    // Without prior clr, out can only hold, increment by 1, or wrap to 0 from MODULUS-1.
    check_no_leap_changes: assert property (
        @(posedge clk) disable iff (clr)
        (!$past(clr)) |-> (
            (out == $past(out)) ||
            (($past(out) == MODULUS-1) && (out == '0)) ||
            (out == $past(out) + 1)
        )
    );

endmodule