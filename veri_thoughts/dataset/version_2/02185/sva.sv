module counter_sva (
    input logic CLK,
    input logic reset,      // Active-high synchronous reset
    input logic enable,
    input logic [3:0] count // 4-bit up-counter
);
    // On reset, next cycle count must be zero.
    reset_clears_next: assert property (
        @(posedge CLK) reset |=> (count == 4'd0)
    );

    // When disabled (and not in reset), hold value next cycle.
    hold_when_disabled: assert property (
        @(posedge CLK) disable iff (reset) (!enable) |=> (count == $past(count))
    );

    // When enabled (and not in reset), increment by 1 next cycle (mod 16).
    increment_when_enabled: assert property (
        @(posedge CLK) disable iff (reset) enable |=> (count == $past(count) + 4'd1)
    );

    // When enabled at max value, wrap to 0 next cycle.
    wrap_on_max: assert property (
        @(posedge CLK) disable iff (reset) (enable && (count == 4'hF)) |=> (count == 4'h0)
    );

    // LSB toggles on each enabled increment.
    lsb_toggle_on_inc: assert property (
        @(posedge CLK) disable iff (reset) enable |=> (count[0] == ~$past(count[0]))
    );

    // Bit1 toggles on increment when there is carry from bit0 (bit0 was 1).
    bit1_toggle_with_carry: assert property (
        @(posedge CLK) disable iff (reset) (enable && (count[0] == 1'b1)) |=> (count[1] == ~$past(count[1]))
    );

    // Bit1 holds on increment when there is no carry from bit0 (bit0 was 0).
    bit1_hold_without_carry: assert property (
        @(posedge CLK) disable iff (reset) (enable && (count[0] == 1'b0)) |=> (count[1] == $past(count[1]))
    );

    // Two consecutive enables cause a net +2 after two cycles (mod 16).
    two_enables_add_two: assert property (
        @(posedge CLK) disable iff (reset) (enable ##1 enable) |=> (count == $past(count, 2) + 4'd2)
    );

    // Two consecutive disables hold the value after two cycles.
    two_disables_hold: assert property (
        @(posedge CLK) disable iff (reset) ((!enable) ##1 (!enable)) |=> (count == $past(count, 2))
    );

    // A rising edge of enable (no reset) causes a +1 next cycle.
    inc_on_enable_rise: assert property (
        @(posedge CLK) disable iff (reset) $rose(enable) |=> (count == $past(count) + 4'd1)
    );
endmodule