module rc_oscillator_sva (
    input logic clk,
    input logic reset,
    input logic osc_out,
    input logic [15:0] count,
    input logic osc_state
);

    ///// Reset behavior /////
    // When reset is asserted, counter/state/output drive to 0.
    check_reset_values: assert property (
        @(posedge clk) reset |-> (count == 16'd0) && (osc_state == 1'b0) && (osc_out == 1'b0)
    );

    ///// Output mapping /////
    // osc_out must always equal osc_state.
    check_out_matches_state: assert property (
        @(posedge clk) disable iff (reset) (osc_out == osc_state)
    );

    ///// Counter next-state rules /////
    // If not wrapping, count increments by 1.
    check_count_increments_no_wrap: assert property (
        @(posedge clk) disable iff (reset)
            ($past(!reset) && ($past(count) != 16'd32768)) |-> (count == $past(count) + 16'd1)
    );

    // When previous count equals 32768, count wraps to 0.
    check_count_wraps_at_limit: assert property (
        @(posedge clk) disable iff (reset)
            ($past(!reset) && ($past(count) == 16'd32768)) |-> (count == 16'd0)
    );

    ///// Oscillator state rules /////
    // On wrap, osc_state toggles.
    check_state_toggles_on_wrap: assert property (
        @(posedge clk) disable iff (reset)
            ($past(!reset) && ($past(count) == 16'd32768)) |-> (osc_state == ~$past(osc_state))
    );

    // If not wrapping, osc_state holds its previous value.
    check_state_holds_no_wrap: assert property (
        @(posedge clk) disable iff (reset)
            ($past(!reset) && ($past(count) != 16'd32768)) |-> (osc_state == $past(osc_state))
    );

    // Any osc_state change implies the previous count was at the wrap value.
    check_state_change_implies_wrap: assert property (
        @(posedge clk) disable iff (reset)
            ($past(!reset) && $changed(osc_state)) |-> ($past(count) == 16'd32768)
    );

    ///// Output behavior derived from state /////
    // On wrap, osc_out toggles (since it mirrors osc_state).
    check_out_toggles_on_wrap: assert property (
        @(posedge clk) disable iff (reset)
            ($past(!reset) && ($past(count) == 16'd32768)) |-> (osc_out != $past(osc_out))
    );

    // If not wrapping, osc_out holds (since osc_state holds).
    check_out_holds_no_wrap: assert property (
        @(posedge clk) disable iff (reset)
            ($past(!reset) && ($past(count) != 16'd32768)) |-> (osc_out == $past(osc_out))
    );

    ///// Additional consistency /////
    // If not in or just after reset, count==0 implies previous count was 32768.
    check_zero_implies_prev_wrap: assert property (
        @(posedge clk) disable iff (reset)
            ($past(!reset) && (count == 16'd0)) |-> ($past(count) == 16'd32768)
    );

endmodule