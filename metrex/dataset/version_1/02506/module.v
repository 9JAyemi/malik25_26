

							parameter
							RESET_PERIOD	=	4
							)
(
input		wire		CLK_I,
input		wire		RST_I,
output	wire		SRST_O
);

reg 	[RESET_PERIOD:0]	RstQ;

initial
		begin
			RstQ[RESET_PERIOD:1]={RESET_PERIOD{1'b1}};
			RstQ[0]=1'b0;
		end

always
RstQ[0] = 1'b0;


genvar i;

		generate
			for(i=1;i<RESET_PERIOD+1;i=i+1)
				always@(posedge CLK_I)
					if(RST_I)
					RstQ[i]	<=	1;
					else
					RstQ[i]	<=	RstQ[i-1];
		endgenerate

	assign SRST_O	=	RstQ[RESET_PERIOD];


endmodule
