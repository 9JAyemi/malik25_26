`define VENDOR_FPGA
module generic_dpram(
	rclk, rrst, rce, oe, raddr, do,
	wclk, wrst, wce, we, waddr, di
);

	parameter aw = 5;  parameter dw = 16; input           rclk;  input           rrst;  input           rce;   input           oe;	   input  [aw-1:0] raddr; output [dw-1:0] do;    input          wclk;  input          wrst;  input          wce;   input          we;    input [aw-1:0] waddr; input [dw-1:0] di;    `ifdef VENDOR_FPGA
	reg [dw-1:0] mem [(1<<aw) -1:0]; reg [aw-1:0] ra;                 always @(posedge rclk)
	  if (rce)
	    ra <= #1 raddr;

	assign do = mem[ra];

	always@(posedge wclk)
		if (we && wce)
			mem[waddr] <= #1 di;

`else

`ifdef VENDOR_XILINX
	xilinx_ram_dp xilinx_ram(
		.CLKA(rclk),
		.RSTA(rrst),
		.ENA(rce),
		.ADDRA(raddr),
		.DIA( {dw{1'b0}} ),
		.WEA(1'b0),
		.DOA(do),

		.CLKB(wclk),
		.RSTB(wrst),
		.ENB(wce),
		.ADDRB(waddr),
		.DIB(di),
		.WEB(we),
		.DOB()
	);

	defparam
		xilinx_ram.dwidth = dw,
		xilinx_ram.awidth = aw;

`else

`ifdef VENDOR_ALTERA
	altera_ram_dp altera_ram(
		.rdclock(rclk),
		.rdclocken(rce),
		.rdaddress(raddr),
		.q(do),

		.wrclock(wclk),
		.wrclocken(wce),
		.wren(we),
		.wraddress(waddr),
		.data(di)
	);

	defparam
		altera_ram.dwidth = dw,
		altera_ram.awidth = aw;

`else

`ifdef VENDOR_ARTISAN

	art_hsdp #(dw, 1<<aw, aw) artisan_sdp(
		.qa(do),
		.clka(rclk),
		.cena(~rce),
		.wena(1'b1),
		.aa(raddr),
		.da( {dw{1'b0}} ),
		.oena(~oe),

		.qb(),
		.clkb(wclk),
		.cenb(~wce),
		.wenb(~we),
		.ab(waddr),
		.db(di),
		.oenb(1'b1)
	);

`else

`ifdef VENDOR_AVANT

	avant_atp avant_atp(
		.web(~we),
		.reb(),
		.oeb(~oe),
		.rcsb(),
		.wcsb(),
		.ra(raddr),
		.wa(waddr),
		.di(di),
		.do(do)
	);

`else

`ifdef VENDOR_VIRAGE

	virage_stp virage_stp(
		.CLKA(rclk),
		.MEA(rce_a),
		.ADRA(raddr),
		.DA( {dw{1'b0}} ),
		.WEA(1'b0),
		.OEA(oe),
		.QA(do),

		.CLKB(wclk),
		.MEB(wce),
		.ADRB(waddr),
		.DB(di),
		.WEB(we),
		.OEB(1'b1),
		.QB()
	);

`else

	reg	[dw-1:0]	mem [(1<<aw)-1:0]; reg	[dw-1:0]	do_reg;            assign do = (oe & rce) ? do_reg : {dw{1'bz}};

	always @(posedge rclk)
		if (rce)
          		do_reg <= #1 (we && (waddr==raddr)) ? {dw{1'b x}} : mem[raddr];

	always @(posedge wclk)
		if (wce && we)
			mem[waddr] <= #1 di;


	task print_ram;
	input [aw-1:0] start;
	input [aw-1:0] finish;
	integer rnum;
  	begin
    		for (rnum=start;rnum<=finish;rnum=rnum+1)
      			$display("Addr %h = %h",rnum,mem[rnum]);
  	end
	endtask

`endif `endif `endif `endif `endif `endif endmodule

`ifdef VENDOR_ALTERA
	module altera_ram_dp(
		data,
		wraddress,
		rdaddress,
		wren,
		wrclock,
		wrclocken,
		rdclock,
		rdclocken,
		q) ;

		parameter awidth = 7;
		parameter dwidth = 8;

		input [dwidth -1:0] data;
		input [awidth -1:0] wraddress;
		input [awidth -1:0] rdaddress;
		input               wren;
		input               wrclock;
		input               wrclocken;
		input               rdclock;
		input               rdclocken;
		output [dwidth -1:0] q;

		syn_dpram_rowr #(
			"UNUSED",
			dwidth,
			awidth,
			1 << awidth
		)
		altera_dpram_model (
			.RdClock(rdclock),
			.RdClken(rdclocken),
			.RdAddress(rdaddress),
			.RdEn(1'b1),
			.Q(q),

			.WrClock(wrclock),
			.WrClken(wrclocken),
			.WrAddress(wraddress),
			.WrEn(wren),
			.Data(data)
		);

		endmodule
`endif `ifdef VENDOR_XILINX
	module xilinx_ram_dp (
		ADDRA,
		CLKA,
		ADDRB,
		CLKB,
		DIA,
		WEA,
		DIB,
		WEB,
		ENA,
		ENB,
		RSTA,
		RSTB,
		DOA,
		DOB)  ;

	parameter awidth = 7;
	parameter dwidth = 8;

	input               CLKA;
	input               RSTA;
	input               ENA;
	input [awidth-1:0]  ADDRA;
	input [dwidth-1:0]  DIA;
	input               WEA;
	output [dwidth-1:0] DOA;

	input               CLKB;
	input               RSTB;
	input               ENB;
	input [awidth-1:0]  ADDRB;
	input [dwidth-1:0]  DIB;
	input               WEB;
	output [dwidth-1:0] DOB;

	C_MEM_DP_BLOCK_V1_0 #(
		awidth,
		awidth,
		1,
		1,
		"0",
		1 << awidth,
		1 << awidth,
		1,
		1,
		1,
		1,
		1,
		1,
		1,
		1,
		1,
		1,
		1,
		1,
		1,
		"",
		16,
		0,
		0,
		1,
		1,
		1,
		1,
		dwidth,
		dwidth)
	xilinx_dpram_model (
		.ADDRA(ADDRA),
		.CLKA(CLKA),
		.ADDRB(ADDRB),
		.CLKB(CLKB),
		.DIA(DIA),
		.WEA(WEA),
		.DIB(DIB),
		.WEB(WEB),
		.ENA(ENA),
		.ENB(ENB),
		.RSTA(RSTA),
		.RSTB(RSTB),
		.DOA(DOA),
		.DOB(DOB));

		endmodule
`endif 