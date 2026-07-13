`define	OPT_DUMBECHO
`ifndef	VERILATOR
`define OPT_STANDALONE
`endif
module	echotest(
		input		i_clk,
`ifndef	OPT_STANDALONE
		input	[30:0]	i_setup,
`endif
		input		i_uart_rx,
		output	wire	o_uart_tx
		);

`ifdef	OPT_DUMBECHO
	reg	r_uart_tx;

	initial	r_uart_tx = 1'b1;
	always @(posedge i_clk)
		r_uart_tx <= i_uart_rx;
	assign	o_uart_tx = r_uart_tx;
	`else
	`ifdef	OPT_STANDALONE
	wire	[30:0]	i_setup;
	assign		i_setup = 31'd868;	`endif
	reg	pwr_reset;
	initial	pwr_reset = 1'b1;
	always @(posedge i_clk)
		pwr_reset = 1'b0;
	wire	rx_stb, rx_break, rx_perr, rx_ferr, rx_ignored;
	wire	[7:0]	rx_data;

`ifdef	USE_LITE_UART
	rxuartlite	#(24'd868)
		receiver(i_clk, i_uart_rx, rx_stb, rx_data);
`else
	rxuart	receiver(i_clk, pwr_reset, i_setup, i_uart_rx, rx_stb, rx_data,
			rx_break, rx_perr, rx_ferr, rx_ignored);
`endif
	wire	cts_n;
	assign cts_n = 1'b0;

	wire	tx_busy;
`ifdef	USE_LITE_UART
	txuartlite #(24'd868)
		transmitter(i_clk, rx_stb, rx_data, o_uart_tx, tx_busy);
`else
	txuart	transmitter(i_clk, pwr_reset, i_setup, rx_break,
			rx_stb, rx_data, rts, o_uart_tx, tx_busy);
`endif
	`endif	endmodule

