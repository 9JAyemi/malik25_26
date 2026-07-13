`define DIV_WITDH 9

module clock_divider(
iCLK,
iRST_n,
oCLK_OUT,
);

input iCLK;
input iRST_n;
output oCLK_OUT;

reg [`DIV_WITDH-1:0] clk_cnt;


always@(posedge iCLK or negedge iRST_n)	
	begin	
		if (!iRST_n)
			clk_cnt <= 0;
		else	
			clk_cnt <= clk_cnt + 1;
	end

assign oCLK_OUT = clk_cnt[`DIV_WITDH-1];


endmodule
