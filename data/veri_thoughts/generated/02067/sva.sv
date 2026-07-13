module mbus_wire_ctrl_sva (
    input logic RESETn,
    input logic DOUT_FROM_BUS,
    input logic CLKOUT_FROM_BUS,
`ifdef POWER_GATING
    input logic DIN,
    input logic CLKIN,
    input logic RELEASE_ISO_FROM_SLEEP_CTRL,
    input logic EXTERNAL_INT,
`endif
    input logic DOUT,
    input logic CLKOUT
);
    // During reset, outputs are forced HIGH.
    reset_outputs_high: assert property (
        @(posedge CLKOUT_FROM_BUS) !RESETn |-> (CLKOUT == 1'b1) && (DOUT == 1'b1)
    );

`ifdef POWER_GATING
    // When ISO hold is active, CLKOUT mirrors CLKIN.
    clkout_select_clkin_when_hold: assert property (
        @(posedge CLKOUT_FROM_BUS) disable iff (!RESETn)
        (RELEASE_ISO_FROM_SLEEP_CTRL == `IO_HOLD) |-> (CLKOUT == CLKIN)
    );
    // When not in ISO hold, CLKOUT mirrors CLKOUT_FROM_BUS.
    clkout_select_bus_when_not_hold: assert property (
        @(posedge CLKOUT_FROM_BUS) disable iff (!RESETn)
        (RELEASE_ISO_FROM_SLEEP_CTRL != `IO_HOLD) |-> (CLKOUT == CLKOUT_FROM_BUS)
    );
    // EXTERNAL_INT forces DOUT LOW.
    dout_forced_low_on_external_int: assert property (
        @(posedge CLKOUT_FROM_BUS) disable iff (!RESETn)
        EXTERNAL_INT |-> (DOUT == 1'b0)
    );
    // Without EXTERNAL_INT and in ISO hold, DOUT mirrors DIN.
    dout_select_din_when_hold_no_int: assert property (
        @(posedge CLKOUT_FROM_BUS) disable iff (!RESETn)
        (!EXTERNAL_INT && (RELEASE_ISO_FROM_SLEEP_CTRL == `IO_HOLD)) |-> (DOUT == DIN)
    );
    // Without EXTERNAL_INT and not in ISO hold, DOUT mirrors DOUT_FROM_BUS.
    dout_select_bus_when_not_hold_no_int: assert property (
        @(posedge CLKOUT_FROM_BUS) disable iff (!RESETn)
        (!EXTERNAL_INT && (RELEASE_ISO_FROM_SLEEP_CTRL != `IO_HOLD)) |-> (DOUT == DOUT_FROM_BUS)
    );
    // If ISO hold and CLKIN are stable, CLKOUT is stable.
    clkout_stable_when_hold_and_clkin_stable: assert property (
        @(posedge CLKOUT_FROM_BUS) disable iff (!RESETn)
        ($stable(RELEASE_ISO_FROM_SLEEP_CTRL) && (RELEASE_ISO_FROM_SLEEP_CTRL == `IO_HOLD) && $stable(CLKIN)) |-> $stable(CLKOUT)
    );
    // If not in ISO hold and bus clock is stable, CLKOUT is stable.
    clkout_stable_when_not_hold_and_busclk_stable: assert property (
        @(posedge CLKOUT_FROM_BUS) disable iff (!RESETn)
        ($stable(RELEASE_ISO_FROM_SLEEP_CTRL) && (RELEASE_ISO_FROM_SLEEP_CTRL != `IO_HOLD) && $stable(CLKOUT_FROM_BUS)) |-> $stable(CLKOUT)
    );
    // If EXTERNAL_INT stays HIGH, DOUT stays LOW.
    dout_stable_low_when_extint_stable_high: assert property (
        @(posedge CLKOUT_FROM_BUS) disable iff (!RESETn)
        ($stable(EXTERNAL_INT) && EXTERNAL_INT) |-> ($stable(DOUT) && (DOUT == 1'b0))
    );
    // If no EXTERNAL_INT, ISO hold and DIN are stable, DOUT is stable.
    dout_stable_when_hold_no_int_and_din_stable: assert property (
        @(posedge CLKOUT_FROM_BUS) disable iff (!RESETn)
        ($stable(EXTERNAL_INT) && !EXTERNAL_INT &&
         $stable(RELEASE_ISO_FROM_SLEEP_CTRL) && (RELEASE_ISO_FROM_SLEEP_CTRL == `IO_HOLD) &&
         $stable(DIN)) |-> $stable(DOUT)
    );
    // If no EXTERNAL_INT, not in ISO hold and bus data is stable, DOUT is stable.
    dout_stable_when_not_hold_no_int_and_busdata_stable: assert property (
        @(posedge CLKOUT_FROM_BUS) disable iff (!RESETn)
        ($stable(EXTERNAL_INT) && !EXTERNAL_INT &&
         $stable(RELEASE_ISO_FROM_SLEEP_CTRL) && (RELEASE_ISO_FROM_SLEEP_CTRL != `IO_HOLD) &&
         $stable(DOUT_FROM_BUS)) |-> $stable(DOUT)
    );
`else
    // When not in reset, CLKOUT mirrors CLKOUT_FROM_BUS.
    clkout_follows_bus_no_pg: assert property (
        @(posedge CLKOUT_FROM_BUS) disable iff (!RESETn)
        (CLKOUT == CLKOUT_FROM_BUS)
    );
    // When not in reset, DOUT mirrors DOUT_FROM_BUS.
    dout_follows_bus_no_pg: assert property (
        @(posedge CLKOUT_FROM_BUS) disable iff (!RESETn)
        (DOUT == DOUT_FROM_BUS)
    );
    // If bus clock is stable, CLKOUT is stable.
    clkout_stable_when_busclk_stable_no_pg: assert property (
        @(posedge CLKOUT_FROM_BUS) disable iff (!RESETn)
        $stable(CLKOUT_FROM_BUS) |-> $stable(CLKOUT)
    );
    // If bus data is stable, DOUT is stable.
    dout_stable_when_busdata_stable_no_pg: assert property (
        @(posedge CLKOUT_FROM_BUS) disable iff (!RESETn)
        $stable(DOUT_FROM_BUS) |-> $stable(DOUT)
    );
`endif
endmodule