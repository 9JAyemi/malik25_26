


module encoderDCAC(clk,
						en,
lasti,	first_blocki,   comp_numberi,   comp_firsti,    comp_colori,    comp_lastinmbi, stb,		zdi,		first_blockz,  zds,		last,		do,
						dv
						);
    input		 clk;
    input		 en;
input		 lasti;
    input       first_blocki;   input [2:0] comp_numberi;   input       comp_firsti;    input       comp_colori;    input       comp_lastinmbi; input		 stb;
    input [12:0] zdi;
    input       first_blockz;  input 		 zds;

    output		  last;

	 output	[15:0]	do;
	 output				dv;

reg			last;

reg  [12:0]   dc_mem[7:0];
    reg  [12:0]   dc_diff0, dc_diff;
    wire [11:0]   dc_diff_limited=  (dc_diff[12]==dc_diff[11])? dc_diff[11:0] : {~dc_diff[11],{11{dc_diff[11]}}}; reg  [12:0]   dc_restored; reg  [5:0]		rll_cntr;
	 reg [15:0]		do;
reg				dv;

reg	[5:0]	cntr;
reg	[11:0] ac_in;

	 wire			izero=(ac_in[11:0]==12'b0);

	 reg	[14:0] val_r;	reg			 DCACen;	wire			 rll_out;
wire			 pre_dv;
	 reg			 was_nonzero_AC;
    reg  [12:0] zdi_d;
    reg   [3:0] zds_d;
wire        DC_tosend=  zds_d[2];
    wire        pre_DCACen= zds_d[1];

    wire  [2:0] comp_numbero;   wire        comp_firsto;    wire        comp_coloro;    wire        comp_lastinmbo; wire        lasto;          reg   [2:0] block_mem_ra;
    reg   [2:0] block_mem_wa;
    reg   [2:0] block_mem_wa_save;
    reg   [6:0] block_mem[0:7];
    wire  [6:0] block_mem_o=block_mem[block_mem_ra[2:0]];
    assign      comp_numbero[2:0]= block_mem_o[2:0];
    assign      comp_firsto=      block_mem_o[3];
    assign      comp_coloro=       block_mem_o[4];
assign      comp_lastinmbo=    block_mem_o[5];
    assign      lasto=             block_mem_o[6];
    always @ (posedge clk) begin
      if (stb) block_mem[block_mem_wa[2:0]] <= {lasti, comp_lastinmbi,  comp_colori,comp_firsti,comp_numberi[2:0]};
      if      (!en) block_mem_wa[2:0] <= 3'h0;
      else if (stb) block_mem_wa[2:0] <= block_mem_wa[2:0] +1;

      if (stb && first_blocki) block_mem_wa_save[2:0] <= block_mem_wa[2:0];

      if      (!en) block_mem_ra[2:0] <= 3'h0;
      else if (zds) block_mem_ra[2:0] <= first_blockz?block_mem_wa_save[2:0]:(block_mem_ra[2:0] +1);
    end

    assign	 rll_out= ((val_r[12] && !val_r[14]) || (ac_in[11:0]!=12'b0)) && (rll_cntr[5:0]!=6'b0);

	 assign	 pre_dv=rll_out || val_r[14] || was_nonzero_AC;

	 always @ (posedge clk) begin
	    val_r[14:0] <={ DC_tosend?
						    {en,
                       comp_coloro,
                       comp_lastinmbo && lasto, dc_diff_limited[11:0]}:
						    {2'b0,
							  (cntr[5:0]==6'h3f),
							  ac_in[11:0]}}; 
		 was_nonzero_AC <= en && (ac_in[11:0]!=12'b0) && DCACen;
		 if (pre_dv) do <= rll_out? {3'b0,val_r[12],6'b0,rll_cntr[5:0]}:{1'b1,val_r[14:0]};
 		 dv	<= pre_dv;
	 	 DCACen	<= en && (pre_DCACen || (DCACen && (cntr[5:0]!=6'h3f)));	if (!DCACen) cntr[5:0] <=6'b0;
		 else			  cntr[5:0] <=cntr[5:0]+1;
	 end

	 always @ (posedge clk) begin
      zdi_d[12:0] <= zdi[12:0];
      ac_in[11:0] <= (zdi_d[12]==zdi_d[11])? zdi_d[11:0]:{~zdi_d[11],{11{zdi_d[11]}}};  if (DC_tosend || !izero || !DCACen) rll_cntr[5:0]	<= 6'h0;
		else if (DCACen) rll_cntr[5:0]	<= rll_cntr[5:0] +1 ;
      if (DC_tosend) last <= lasto;
	 end

always @ (posedge clk) begin
      zds_d[3:0]           <= {zds_d[2:0], zds};
	 	if (zds_d[0])   dc_diff0[12:0] <= comp_firsto?13'b0:dc_mem[comp_numbero[2:0]];
		if (zds_d[1])   dc_diff [12:0] <= zdi_d[12:0]-dc_diff0[12:0];
      if (zds_d[2])   dc_restored[12:0] <=  dc_diff0[12:0] + {dc_diff_limited[11],dc_diff_limited[11:0]};
      if (zds_d[3])   dc_mem[comp_numbero[2:0]]   <= dc_restored[12:0];
	 end


endmodule
