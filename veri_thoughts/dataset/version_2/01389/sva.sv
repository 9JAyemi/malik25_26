module counter_sva #(
    parameter WIDTH = 8,
    parameter MODULUS = 256
)(
    input  logic                 ce,
    input  logic                 clr,
    input  logic                 clk,
    input  logic [WIDTH-1:0]     out
);
    // Local constants sized to WIDTH
    localparam logic [WIDTH-1:0] MODM1 = MODULUS - 1;
    localparam logic [WIDTH-1:0] ZERO  = {WIDTH{1'b0}};

    ///// Synchronous clear behavior /////
    // On clr, out is 0 on the next cycle (clr overrides ce).
    check_sync_clear_sets_zero: assert property (
        @(posedge clk) clr |=> (out == ZERO)
    );

    ///// Normal operation (disable during clr) /////
    // With ce low and no clr, out holds its value.
    check_hold_when_ce_low: assert property (
        @(posedge clk) disable iff (clr) (!ce) |=> (out == $past(out))
    );

    // With ce high and not at MOD-1, out increments by 1.
    check_increment_when_enabled_nonmax: assert property (
        @(posedge clk) disable iff (clr) (ce && (out != MODM1)) |=> (out == $past(out) + 1)
    );

    // With ce high at MOD-1, out wraps to 0.
    check_wrap_when_enabled_at_max: assert property (
        @(posedge clk) disable iff (clr) (ce && (out == MODM1)) |=> (out == ZERO)
    );

    // Any change in out must be due to prior ce or clr.
    check_change_requires_enable_or_clear: assert property (
        @(posedge clk) (out != $past(out)) |-> ($past(ce) || $past(clr))
    );

    // Transition to 0 from nonzero without clr implies wrap due to ce at MOD-1.
    check_zero_transition_cause: assert property (
        @(posedge clk)
            (!$past(clr) && ($past(out) != ZERO) && (out == ZERO)) |-> ($past(ce) && ($past(out) == MODM1))
    );

    // With ce high and no clr, next out is either prev+1 or wraps to 0.
    check_enable_defines_next_state: assert property (
        @(posedge clk) disable iff (clr)
            ce |=> ((($past(out) != MODM1) && (out == $past(out) + 1)) ||
                    (($past(out) == MODM1) && (out == ZERO)))
    );
endmodule