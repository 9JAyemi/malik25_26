module slow_oscillator_sva (
    input logic rstn,
    input logic osc_clk,
    input logic [3:0] led,
    input logic clk
);
    ///// Reset behavior on clk /////
    // While reset is asserted low, clk must be 0.
    reset_drives_clk_low: assert property (
        @(posedge osc_clk) !rstn |-> (clk == 1'b0)
    );

    // On the cycle reset is released, clk is 0.
    clk_low_on_reset_release: assert property (
        @(posedge osc_clk) disable iff (!rstn) $rose(rstn) |-> (clk == 1'b0)
    );

    ///// clk timing derived from c_delay MSB /////
    // clk cannot toggle on two consecutive osc_clk cycles (MSB of counter cannot toggle back-to-back).
    clk_no_back_to_back_toggles: assert property (
        @(posedge osc_clk) disable iff (!rstn) $changed(clk) |-> ##1 !$changed(clk)
    );

    ///// led behavior from grey_counter_4bit /////
    // If previous led was 0xF, next led must wrap to 0x0.
    led_wrap_from_15_to_0: assert property (
        @(posedge osc_clk) disable iff (!rstn)
            (!$isunknown($past(led)) && ($past(led) == 4'hF)) |-> (led == 4'h0)
    );

    // If previous led was not 0xF, next led must increment by 1.
    led_increments_non_wrap: assert property (
        @(posedge osc_clk) disable iff (!rstn)
            (!$isunknown($past(led)) && ($past(led) != 4'hF)) |-> (led == ($past(led) + 4'd1))
    );

    // When known, led must change every osc_clk cycle (free-running incrementer).
    led_changes_each_cycle_when_known: assert property (
        @(posedge osc_clk) disable iff (!rstn)
            (!$isunknown($past(led)) && !$isunknown(led)) |-> (led != $past(led))
    );

    // If previous led is known, next led must also be known (no X/Z creation from the counter).
    led_known_propagates_from_known: assert property (
        @(posedge osc_clk) disable iff (!rstn)
            (!$isunknown($past(led))) |-> (!$isunknown(led))
    );

    // If current led is 0x0 and known, previous must have been 0xF.
    led_zero_prev_was_15: assert property (
        @(posedge osc_clk) disable iff (!rstn)
            (!$isunknown(led) && (led == 4'h0) && !$isunknown($past(led))) |-> ($past(led) == 4'hF)
    );

    // If current led is non-zero and known, previous must be current-1.
    led_nonzero_prev_is_minus_one: assert property (
        @(posedge osc_clk) disable iff (!rstn)
            (!$isunknown(led) && (led != 4'h0) && !$isunknown($past(led))) |-> ($past(led) == (led - 4'd1))
    );

    // The LSB of led toggles every osc_clk cycle when known (increment by 1).
    led_lsb_toggles_every_cycle: assert property (
        @(posedge osc_clk) disable iff (!rstn)
            (!$isunknown($past(led[0])) && !$isunknown(led[0])) |-> (led[0] != $past(led[0]))
    );

endmodule