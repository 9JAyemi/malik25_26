

module RCB_FRL_TrainingPattern(
		CLK,
		RST,
		DATA_OUT);
		
	input		CLK, RST;
	output reg [7:0]	DATA_OUT;
	
	always @ (posedge CLK)
	begin
		if(RST)
		begin
			DATA_OUT <= 0;
		end
		else
		begin
			if(DATA_OUT == 8'hf4)
				DATA_OUT <= 8'hc2;
			else
				DATA_OUT <= 8'hf4;
		end
	end
	
endmodule
	