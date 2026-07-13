module Comparador_sva (
    input logic clock,
    input logic reset,
    input logic [3:0] write_value,
    input logic [3:0] read_value,
    input logic read_value_reg_en,
    input logic led_success,
    input logic led_fail,
    // Internal signal from RTL (bind or connect hierarchically)
    input logic [3:0] read_value_reg
);
    // Clock: clock (posedge). Reset: reset (active-high, async). Mixed logic: reg + combinational compares.

    ///// Register behavior /////
    // While reset is asserted, read_value_reg is held at 0.
    reset_clears_reg: assert property (
        @(posedge clock) reset |-> (read_value_reg == 4'b0000)
    );
    // When enabled, next cycle read_value_reg updates from read_value.
    load_on_enable: assert property (
        @(posedge clock) disable iff (reset) read_value_reg_en |=> (read_value_reg == $past(read_value))
    );
    // If enable stays LOW across two cycles, the register holds its value.
    hold_when_enable_stays_low: assert property (
        @(posedge clock) disable iff (reset) (!read_value_reg_en ##1 !read_value_reg_en) |-> (read_value_reg == $past(read_value_reg,1))
    );

    ///// LED definitions /////
    // led_fail is always the logical inverse of led_success.
    led_fail_is_invert_success: assert property (
        @(posedge clock) disable iff (reset) (led_fail == ~led_success)
    );
    // led_success reflects write_value == read_value_reg.
    led_success_matches_compare: assert property (
        @(posedge clock) disable iff (reset) (led_success == (write_value == read_value_reg))
    );
    // During reset (read_value_reg forced to 0), LEDs reflect compare against zero.
    leds_match_zero_during_reset: assert property (
        @(posedge clock) reset |-> (led_success == (write_value == 4'b0000)) && (led_fail == ~(write_value == 4'b0000))
    );
    // Exactly one of the LEDs is HIGH (mutual exclusion and completeness).
    leds_one_hot: assert property (
        @(posedge clock) disable iff (reset) (led_success ^ led_fail)
    );

    ///// LED response to register update /////
    // After an enabled load, next-cycle led_success matches write_value vs prior-cycle read_value.
    led_success_updates_after_enable: assert property (
        @(posedge clock) disable iff (reset) read_value_reg_en |=> (led_success == (write_value == $past(read_value)))
    );
    // If enable stays LOW and write_value is stable across two cycles, LEDs remain stable.
    leds_stable_when_inputs_stable: assert property (
        @(posedge clock) disable iff (reset)
            ((!read_value_reg_en && $stable(write_value)) ##1 (!read_value_reg_en && $stable(write_value)))
            |-> (led_success == $past(led_success,1)) && (led_fail == $past(led_fail,1))
    );

endmodule