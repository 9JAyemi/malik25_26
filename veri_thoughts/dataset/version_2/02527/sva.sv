module Register_sva (
    input logic Bus_in,
    input logic clk,
    input logic reset,
    input logic r_in,
    input logic r_out,
    input logic Bus_out,
    input logic reg_data
);
    ///// Reset behavior /////
    // During reset, the internal register is cleared to 0.
    reset_clears_reg: assert property (
        @(posedge clk) reset |-> (reg_data == 1'b0)
    );
    // During reset, Bus_out is forced low.
    reset_forces_busout_low: assert property (
        @(posedge clk) reset |-> (Bus_out == 1'b0)
    );

    ///// Output gating /////
    // Bus_out implements a mux: r_out ? reg_data : 1'b0.
    check_busout_mux_eq: assert property (
        @(posedge clk) (Bus_out == (r_out ? reg_data : 1'b0))
    );
    // If Bus_out is HIGH, r_out must be HIGH.
    check_busout_high_requires_enable: assert property (
        @(posedge clk) (Bus_out == 1'b1) |-> (r_out == 1'b1)
    );
    // If Bus_out is HIGH, reg_data must be HIGH.
    check_busout_high_requires_data: assert property (
        @(posedge clk) (Bus_out == 1'b1) |-> (reg_data == 1'b1)
    );

    ///// Combinational consistency /////
    // Bus_out only changes if r_out or reg_data changes.
    check_busout_change_caused_by_inputs: assert property (
        @(posedge clk) $changed(Bus_out) |-> ($changed(r_out) || $changed(reg_data))
    );
    // If r_out and reg_data are stable, Bus_out is stable.
    check_busout_stable_when_inputs_stable: assert property (
        @(posedge clk) ($stable(r_out) && $stable(reg_data)) |-> $stable(Bus_out)
    );

    ///// Register update semantics /////
    // On write enable, next reg_data equals current Bus_in.
    check_write_captures_bus_in: assert property (
        @(posedge clk) disable iff (reset) r_in |=> (reg_data == $past(Bus_in))
    );
    // Without write enable, reg_data holds its previous value.
    check_hold_without_write: assert property (
        @(posedge clk) disable iff (reset) !r_in |=> (reg_data == $past(reg_data))
    );

    ///// Interaction of read enable with stability /////
    // If r_out stays HIGH and no write this cycle, Bus_out remains stable.
    check_busout_stable_when_enabled_and_no_write: assert property (
        @(posedge clk) disable iff (reset) (!r_in && $past(r_out) && r_out) |-> $stable(Bus_out)
    );
    // If r_out is HIGH in consecutive cycles and reg_data changes, Bus_out changes.
    check_busout_tracks_reg_when_enabled: assert property (
        @(posedge clk) disable iff (reset) ($past(r_out) && r_out && $changed(reg_data)) |-> $changed(Bus_out)
    );
endmodule