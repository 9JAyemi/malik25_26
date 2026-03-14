module de_PLL_sva (
    input logic areset,
    input logic inclk0,
    input logic c0,

    // Internal signals from RTL (bind/connect hierarchically)
    input logic        phase_error,
    input logic        phase_error_d1,
    input logic [7:0]  charge_pump_out,
    input logic [15:0] loop_filter_out,
    input logic [31:0] vco_out,
    input logic [31:0] div_by_2_out
);

    ///// Reset behavior /////
    // During reset, c0 must be LOW.
    reset_c0_low: assert property (
        @(posedge inclk0) (!areset) |-> (c0 == 1'b0)
    );
    // During reset, phase_error_d1 must be 0.
    reset_phase_error_d1_zero: assert property (
        @(posedge inclk0) (!areset) |-> (phase_error_d1 == 1'b0)
    );
    // During reset, charge_pump_out must be 0.
    reset_charge_pump_zero: assert property (
        @(posedge inclk0) (!areset) |-> (charge_pump_out == 8'h00)
    );
    // During reset, loop_filter_out must be 0.
    reset_loop_filter_zero: assert property (
        @(posedge inclk0) (!areset) |-> (loop_filter_out == 16'h0000)
    );
    // During reset, vco_out must be 0.
    reset_vco_zero: assert property (
        @(posedge inclk0) (!areset) |-> (vco_out == 32'h00000000)
    );
    // During reset, div_by_2_out must be 0.
    reset_div2_zero: assert property (
        @(posedge inclk0) (!areset) |-> (div_by_2_out == 32'h00000000)
    );

    ///// Phase detector /////
    // phase_error is combinational: (c0 & ~inclk0) | (~c0 & inclk0).
    comb_phase_error_def: assert property (
        @(posedge inclk0) disable iff (!areset) phase_error == ((c0 & ~inclk0) | (~c0 & inclk0))
    );
    // phase_error_d1 is one-cycle delayed sample of phase_error.
    pipe_phase_error_d1: assert property (
        @(posedge inclk0) disable iff (!areset) $past(areset) |-> (phase_error_d1 == $past(phase_error))
    );

    ///// Charge pump /////
    // charge_pump_out next-state matches saturating up/down rules.
    cp_nextstate_match: assert property (
        @(posedge inclk0) disable iff (!areset)
            $past(areset) |-> charge_pump_out ==
                ((phase_error && ($past(charge_pump_out) < 8'h7F)) ? ($past(charge_pump_out) + 8'd1) :
                 ((!phase_error && ($past(charge_pump_out) > 8'h80)) ? ($past(charge_pump_out) - 8'd1) :
                  $past(charge_pump_out)))
    );
    // charge_pump_out step size is at most +/-1 per cycle.
    cp_step_bound: assert property (
        @(posedge inclk0) disable iff (!areset)
            $past(areset) |-> (
                (charge_pump_out == $past(charge_pump_out)) ||
                (charge_pump_out == ($past(charge_pump_out) + 8'd1)) ||
                (charge_pump_out == ($past(charge_pump_out) - 8'd1))
            )
    );

    ///// Loop filter /////
    // loop_filter_out accumulates previous charge_pump_out.
    lf_accumulate: assert property (
        @(posedge inclk0) disable iff (!areset)
            $past(areset) |-> (loop_filter_out == ($past(loop_filter_out) + $past(charge_pump_out)))
    );

    ///// VCO /////
    // vco_out accumulates previous loop_filter_out.
    vco_accumulate: assert property (
        @(posedge inclk0) disable iff (!areset)
            $past(areset) |-> (vco_out == ($past(vco_out) + $past(loop_filter_out)))
    );

    ///// Divide-by-2 and output /////
    // c0 is the MSB of div_by_2_out.
    c0_matches_div2_msb: assert property (
        @(posedge inclk0) disable iff (!areset) (c0 == div_by_2_out[31])
    );

endmodule