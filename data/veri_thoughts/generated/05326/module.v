module	wbdblpriarb(i_clk, i_rst,
	i_a_cyc_a,i_a_cyc_b,i_a_stb_a,i_a_stb_b,i_a_we,i_a_adr, i_a_dat, i_a_sel, o_a_ack, o_a_stall, o_a_err,
	i_b_cyc_a,i_b_cyc_b,i_b_stb_a,i_b_stb_b,i_b_we,i_b_adr, i_b_dat, i_b_sel, o_b_ack, o_b_stall, o_b_err,
	o_cyc_a, o_cyc_b, o_stb_a, o_stb_b, o_we, o_adr, o_dat, o_sel,
		i_ack, i_stall, i_err);
	parameter			DW=32, AW=32;
	input	wire			i_clk, i_rst;
	input	wire			i_a_cyc_a, i_a_cyc_b, i_a_stb_a, i_a_stb_b, i_a_we;
	input	wire	[(AW-1):0]	i_a_adr;
	input	wire	[(DW-1):0]	i_a_dat;
	input	wire	[(DW/8-1):0]	i_a_sel;
	output	wire			o_a_ack, o_a_stall, o_a_err;
	input	wire			i_b_cyc_a, i_b_cyc_b, i_b_stb_a, i_b_stb_b, i_b_we;
	input	wire	[(AW-1):0]	i_b_adr;
	input	wire	[(DW-1):0]	i_b_dat;
	input	wire	[(DW/8-1):0]	i_b_sel;
	output	wire			o_b_ack, o_b_stall, o_b_err;
	output	wire			o_cyc_a,o_cyc_b, o_stb_a, o_stb_b, o_we;
	output	wire	[(AW-1):0]	o_adr;
	output	wire	[(DW-1):0]	o_dat;
	output	wire	[(DW/8-1):0]	o_sel;
	input	wire			i_ack, i_stall, i_err;

	reg r_a_owner;
	assign o_cyc_a = ((r_a_owner) ? i_a_cyc_a : i_b_cyc_a);
	assign o_cyc_b = ((r_a_owner) ? i_a_cyc_b : i_b_cyc_b);
	initial	r_a_owner = 1'b1;
	always @(posedge i_clk)
		if (i_rst)
			r_a_owner <= 1'b1;
		
		else if ((!i_b_cyc_a)&&(!i_b_cyc_b))
			r_a_owner <= 1'b1;
		else if ((!i_a_cyc_a)&&(!i_a_cyc_b)
				&&((i_b_stb_a)||(i_b_stb_b)))
			r_a_owner <= 1'b0;


	assign o_we    = (r_a_owner) ? i_a_we    : i_b_we;
`ifdef	ZERO_ON_IDLE
	wire	o_cyc, o_stb;
	assign	o_cyc     = ((o_cyc_a)||(o_cyc_b));
	assign	o_stb     = (o_cyc)&&((o_stb_a)||(o_stb_b));
	assign	o_stb_a   = (r_a_owner) ? (i_a_stb_a)&&(o_cyc_a) : (i_b_stb_a)&&(o_cyc_a);
	assign	o_stb_b   = (r_a_owner) ? (i_a_stb_b)&&(o_cyc_b) : (i_b_stb_b)&&(o_cyc_b);
	assign	o_adr     = ((o_stb_a)|(o_stb_b))?((r_a_owner) ? i_a_adr   : i_b_adr):0;
	assign	o_dat     = (o_stb)?((r_a_owner) ? i_a_dat   : i_b_dat):0;
	assign	o_sel     = (o_stb)?((r_a_owner) ? i_a_sel   : i_b_sel):0;
	assign	o_a_ack   = (o_cyc)&&( r_a_owner) ? i_ack   : 1'b0;
	assign	o_b_ack   = (o_cyc)&&(!r_a_owner) ? i_ack   : 1'b0;
	assign	o_a_stall = (o_cyc)&&( r_a_owner) ? i_stall : 1'b1;
	assign	o_b_stall = (o_cyc)&&(!r_a_owner) ? i_stall : 1'b1;
	assign	o_a_err   = (o_cyc)&&( r_a_owner) ? i_err : 1'b0;
	assign	o_b_err   = (o_cyc)&&(!r_a_owner) ? i_err : 1'b0;
`else
	assign o_stb_a = (r_a_owner) ? i_a_stb_a : i_b_stb_a;
	assign o_stb_b = (r_a_owner) ? i_a_stb_b : i_b_stb_b;
	assign o_adr   = (r_a_owner) ? i_a_adr   : i_b_adr;
	assign o_dat   = (r_a_owner) ? i_a_dat   : i_b_dat;
	assign o_sel   = (r_a_owner) ? i_a_sel   : i_b_sel;

	assign	o_a_ack   = ( r_a_owner) ? i_ack   : 1'b0;
	assign	o_b_ack   = (!r_a_owner) ? i_ack   : 1'b0;

	assign	o_a_stall = ( r_a_owner) ? i_stall : 1'b1;
	assign	o_b_stall = (!r_a_owner) ? i_stall : 1'b1;

	assign	o_a_err = ( r_a_owner) ? i_err : 1'b0;
	assign	o_b_err = (!r_a_owner) ? i_err : 1'b0;
`endif

endmodule

