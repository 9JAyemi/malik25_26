`define	WBA_ALTERNATING
module	wbarbiter(i_clk, i_rst, 
	i_a_cyc, i_a_stb, i_a_we, i_a_adr, i_a_dat, i_a_sel, o_a_ack, o_a_stall, o_a_err,
	i_b_cyc, i_b_stb, i_b_we, i_b_adr, i_b_dat, i_b_sel, o_b_ack, o_b_stall, o_b_err,
	o_cyc, o_stb, o_we, o_adr, o_dat, o_sel, i_ack, i_stall, i_err);
	parameter			DW=32, AW=19;
	input	wire			i_clk, i_rst;
	input	wire			i_a_cyc, i_a_stb, i_a_we;
	input	wire	[(AW-1):0]	i_a_adr;
	input	wire	[(DW-1):0]	i_a_dat;
	input	wire	[(DW/8-1):0]	i_a_sel;
	output	wire			o_a_ack, o_a_stall, o_a_err;
	input	wire			i_b_cyc, i_b_stb, i_b_we;
	input	wire	[(AW-1):0]	i_b_adr;
	input	wire	[(DW-1):0]	i_b_dat;
	input	wire	[(DW/8-1):0]	i_b_sel;
	output	wire			o_b_ack, o_b_stall, o_b_err;
	output	wire			o_cyc, o_stb, o_we;
	output	wire	[(AW-1):0]	o_adr;
	output	wire	[(DW-1):0]	o_dat;
	output	wire	[(DW/8-1):0]	o_sel;
	input	wire			i_ack, i_stall, i_err;

	reg	r_cyc;
	always @(posedge i_clk)
		if (i_rst)
			r_cyc <= 1'b0;
		else
			r_cyc <= o_cyc;

	wire	w_a_owner, w_b_owner;   
	assign o_cyc = ((~r_cyc)&&((i_a_cyc)||(i_b_cyc))) || ((r_cyc)&&((w_a_owner)||(w_b_owner)));


	reg	r_a_owner, r_b_owner;
`ifdef	WBA_ALTERNATING
	reg	r_a_last_owner;

`endif
	always @(posedge i_clk)
		if (i_rst)
		begin
			r_a_owner <= 1'b0;
			r_b_owner <= 1'b0;
		end else begin
			r_a_owner <= w_a_owner;
			r_b_owner <= w_b_owner;
`ifdef	WBA_ALTERNATING
			if (w_a_owner)
				r_a_last_owner <= 1'b1;
			else if (w_b_owner)
				r_a_last_owner <= 1'b0;
`endif
		end
	`ifdef	WBA_ALTERNATING
	assign w_a_owner = (i_a_cyc)	&& ((r_a_owner) || ((~r_cyc) &&((~i_b_cyc) ||(~r_a_last_owner)) )); assign w_b_owner = (i_b_cyc)&& ((r_b_owner) || ((~r_cyc)&&((~i_a_cyc)||(r_a_last_owner)) ));
`else
	assign w_a_owner = (i_a_cyc)&& ((r_a_owner) ||  (~r_cyc) );
	assign w_b_owner = (i_b_cyc)&& ((r_b_owner) || ((~r_cyc)&&(~i_a_cyc)) );
`endif

	assign o_stb = (o_cyc) && ((w_a_owner) ? i_a_stb : i_b_stb);
	assign o_we  = (w_a_owner) ? i_a_we  : i_b_we;
	assign o_adr = (w_a_owner) ? i_a_adr : i_b_adr;
	assign o_dat = (w_a_owner) ? i_a_dat : i_b_dat;
	assign o_sel = (w_a_owner) ? i_a_sel : i_b_sel;

	assign	o_a_ack   = (w_a_owner) ? i_ack   : 1'b0;
	assign	o_b_ack   = (w_b_owner) ? i_ack   : 1'b0;

	assign	o_a_stall = (w_a_owner) ? i_stall : 1'b1;
	assign	o_b_stall = (w_b_owner) ? i_stall : 1'b1;

	assign	o_a_err = (w_a_owner) ? i_err : 1'b0;
	assign	o_b_err = (w_b_owner) ? i_err : 1'b0;

endmodule

