

`include "ac97_defines.v"

module ac97_rst(clk, rst, rst_force, ps_ce, ac97_rst_);
input		clk, rst;
input		rst_force;
output		ps_ce;
output		ac97_rst_;

reg		ac97_rst_;
reg	[2:0]	cnt;
wire		ce;
wire		to;
reg	[5:0]	ps_cnt;
wire		ps_ce;

always @(posedge clk or negedge rst)
	if(!rst)	ac97_rst_ <= #1 0;
	else
	if(rst_force)	ac97_rst_ <= #1 0;
	else
	if(to)		ac97_rst_ <= #1 1;

assign to = (cnt == `AC97_RST_DEL);

always @(posedge clk or negedge rst)
	if(!rst)	cnt <= #1 0;
	else
	if(rst_force)	cnt <= #1 0;
	else
	if(ce)		cnt <= #1 cnt + 1;

assign ce = ps_ce & (cnt != `AC97_RST_DEL);

always @(posedge clk or negedge rst)
	if(!rst)		ps_cnt <= #1 0;
	else
	if(ps_ce | rst_force)	ps_cnt <= #1 0;
	else			ps_cnt <= #1 ps_cnt + 1;

assign ps_ce = (ps_cnt == `AC97_250_PS);

endmodule
