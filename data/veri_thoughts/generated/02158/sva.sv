module frequency_divider_sva #(
    parameter int PRESET_VALUE = 100
) (
    input  logic clk,
    input  logic reset,
    input  logic data,
    input  logic pulse,
    input  logic [PRESET_VALUE-1:0] shift_reg,
    input  logic [7:0] counter
);
    ///// Reset behavior /////
    // On synchronous reset, all state clears to 0.
    reset_clears_state: assert property (
        @(posedge clk) reset |-> (shift_reg == '0) && (counter == 8'd0) && (pulse == 1'b0)
    );

    ///// Shift register behavior /////
    // shift_reg shifts in 'data' at MSB each cycle when not in reset.
    shift_reg_shifts_in_data: assert property (
        @(posedge clk) disable iff (reset) shift_reg == {data, $past(shift_reg)[PRESET_VALUE-2:0]}
    );

    ///// Counter behavior /////
    // Counter increments by 1 when previous value is not PRESET_VALUE-1.
    counter_increments_when_not_terminal: assert property (
        @(posedge clk) disable iff (reset) ($past(counter) != PRESET_VALUE-1) |-> (counter == $past(counter) + 8'd1)
    );

    // Counter resets to 0 when previous value is PRESET_VALUE-1.
    counter_resets_at_terminal: assert property (
        @(posedge clk) disable iff (reset) ($past(counter) == PRESET_VALUE-1) |-> (counter == 8'd0)
    );

    // Counter never exceeds PRESET_VALUE-1 (for PRESET_VALUE <= 256 this is exact).
    counter_bounded_by_preset: assert property (
        @(posedge clk) disable iff (reset) counter <= PRESET_VALUE-1
    );

    ///// Pulse generation behavior /////
    // Pulse toggles exactly when previous counter equals PRESET_VALUE-1.
    pulse_toggles_at_terminal_count: assert property (
        @(posedge clk) disable iff (reset) ($past(counter) == PRESET_VALUE-1) |-> (pulse == ~$past(pulse))
    );

    // Pulse holds value when previous counter is not PRESET_VALUE-1.
    pulse_holds_when_not_terminal: assert property (
        @(posedge clk) disable iff (reset) ($past(counter) != PRESET_VALUE-1) |-> (pulse == $past(pulse))
    );

    // Any pulse change implies counter is 0 on this cycle.
    pulse_change_implies_counter_zero: assert property (
        @(posedge clk) disable iff (reset) (pulse != $past(pulse)) |-> (counter == 8'd0)
    );

    // Successive pulse toggles are PRESET_VALUE cycles apart (absent reset).
    pulse_period_is_PRESET_VALUE: assert property (
        @(posedge clk) disable iff (reset) (pulse != $past(pulse)) |-> ##PRESET_VALUE (pulse != $past(pulse))
    );

    // After reset deassertion, the next pulse toggle occurs in exactly PRESET_VALUE cycles.
    first_toggle_after_reset: assert property (
        @(posedge clk) disable iff (reset) $fell(reset) |-> ##PRESET_VALUE (pulse != $past(pulse))
    );
endmodule