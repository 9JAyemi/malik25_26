module data_whiting_sva (
    input  logic        clk,
    input  logic        reset_n,
    input  logic [7:0]  din,
    input  logic        indicator,
    input  logic [7:0]  dout,
    input  logic        next_indicator
);
    ///// Indicator pass-through /////
    // next_indicator equals indicator in normal operation.
    check_next_indicator_passthrough: assert property (
        @(posedge clk) disable iff (!reset_n) (next_indicator === indicator)
    );
    // next_indicator equals indicator during reset.
    check_next_indicator_passthrough_during_reset: assert property (
        @(posedge clk) (!reset_n) |-> (next_indicator === indicator)
    );
    // Rising edge on indicator must reflect on next_indicator.
    check_next_indicator_rise_match: assert property (
        @(posedge clk) disable iff (!reset_n) $rose(indicator) |-> $rose(next_indicator)
    );
    // Falling edge on indicator must reflect on next_indicator.
    check_next_indicator_fall_match: assert property (
        @(posedge clk) disable iff (!reset_n) $fell(indicator) |-> $fell(next_indicator)
    );
    // No spurious rising edge on next_indicator without indicator rising.
    check_no_spurious_rise_on_next_indicator: assert property (
        @(posedge clk) disable iff (!reset_n) $rose(next_indicator) |-> $rose(indicator)
    );
    // No spurious falling edge on next_indicator without indicator falling.
    check_no_spurious_fall_on_next_indicator: assert property (
        @(posedge clk) disable iff (!reset_n) $fell(next_indicator) |-> $fell(indicator)
    );
    // If indicator is stable, next_indicator must be stable.
    check_stable_indicator_implies_stable_next: assert property (
        @(posedge clk) disable iff (!reset_n) $stable(indicator) |-> $stable(next_indicator)
    );
    // If next_indicator is stable, indicator must be stable (pure pass-through).
    check_stable_next_implies_stable_indicator: assert property (
        @(posedge clk) disable iff (!reset_n) $stable(next_indicator) |-> $stable(indicator)
    );

    ///// Reset behavior /////
    // While reset is asserted, dout equals din (state forced to WAITING).
    check_dout_equals_din_during_reset: assert property (
        @(posedge clk) (!reset_n) |-> (dout === din)
    );
endmodule