
module mbus_wire_ctrl(
	input RESETn,
	input DOUT_FROM_BUS,
	input CLKOUT_FROM_BUS,
	`ifdef POWER_GATING
	input DIN,
	input CLKIN,
	input RELEASE_ISO_FROM_SLEEP_CTRL,
	input EXTERNAL_INT,
	`endif
	output reg DOUT,
	output reg CLKOUT
);

`ifdef POWER_GATING
always @ *
begin
	if (~RESETn)
		CLKOUT <= 1'b1;
	else if (RELEASE_ISO_FROM_SLEEP_CTRL==`IO_HOLD)
		CLKOUT <= CLKIN;
	else
		CLKOUT <= CLKOUT_FROM_BUS;

	if (~RESETn)
		DOUT <= 1'b1;
	else if (EXTERNAL_INT)
		DOUT <= 0;
	else
	begin
		if (RELEASE_ISO_FROM_SLEEP_CTRL==`IO_HOLD)
			DOUT <= DIN;
		else
			DOUT <= DOUT_FROM_BUS;
	end
end
`else
always @ *
begin
	if (~RESETn)
		CLKOUT <= 1'b1;
	else
		CLKOUT <= CLKOUT_FROM_BUS;

	if (~RESETn)
		DOUT <= 1'b1;
	else
		DOUT <= DOUT_FROM_BUS;
end
`endif

endmodule