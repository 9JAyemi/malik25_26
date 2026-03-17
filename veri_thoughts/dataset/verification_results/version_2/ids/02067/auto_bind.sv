// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_outputs_high, assert, property, posedge, b1, clkout_select_clkin_when_hold, disable, iff, IO_HOLD, clkout_select_bus_when_not_hold, dout_forced_low_on_external_int, b0, dout_select_din_when_hold_no_int, dout_select_bus_when_not_hold_no_int, clkout_stable_when_hold_and_clkin_stable, stable, clkout_stable_when_not_hold_and_busclk_stable, dout_stable_low_when_extint_stable_high, dout_stable_when_hold_no_int_and_din_stable, dout_stable_when_not_hold_no_int_and_busdata_stable, else, clkout_follows_bus_no_pg, dout_follows_bus_no_pg, clkout_stable_when_busclk_stable_no_pg, dout_stable_when_busdata_stable_no_pg
bind mbus_wire_ctrl mbus_wire_ctrl_sva auto_sva_inst (
    .RESETn(RESETn),
    .DOUT_FROM_BUS(DOUT_FROM_BUS),
    .CLKOUT_FROM_BUS(CLKOUT_FROM_BUS),
    .ifdef(ifdef),
    .POWER_GATING(POWER_GATING),
    .DIN(DIN),
    .CLKIN(CLKIN),
    .RELEASE_ISO_FROM_SLEEP_CTRL(RELEASE_ISO_FROM_SLEEP_CTRL),
    .EXTERNAL_INT(EXTERNAL_INT),
    .endif(endif),
    .DOUT(DOUT),
    .CLKOUT(CLKOUT)
);
