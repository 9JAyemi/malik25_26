

module DisplayCtrl(Clk, reset, memoryData,
		An0, An1, An2, An3, Ca, Cb, Cc, Cd, Ce, Cf, Cg, Dp
   );
	
	input [26:0] Clk;
	input reset;
	input [15:0] memoryData;
	output An0, An1, An2, An3, Ca, Cb, Cc, Cd, Ce, Cf, Cg, Dp;

	reg [6:0] SSD_CATHODES;
	wire [26:0] DIV_CLK;
	reg [3:0] SSD;
	wire [3:0] SSD0, SSD1, SSD2, SSD3;
	wire [1:0] ssdscan_clk;
	
	assign {Ca, Cb, Cc, Cd, Ce, Cf, Cg, Dp} = {SSD_CATHODES, 1'b1};
	assign DIV_CLK = Clk;

	assign SSD3 = memoryData[15:12];
	assign SSD2 = memoryData[11:8];
	assign SSD1 = memoryData[7:4];
	assign SSD0 = memoryData[3:0];

	assign ssdscan_clk = DIV_CLK[19:18];	
	assign An0 = !(~(ssdscan_clk[1]) && ~(ssdscan_clk[0]));  assign An1 = !(~(ssdscan_clk[1]) &&  (ssdscan_clk[0]));  assign An2 = !( (ssdscan_clk[1]) && ~(ssdscan_clk[0]));  assign An3 = !( (ssdscan_clk[1]) &&  (ssdscan_clk[0]));  always @ (ssdscan_clk, SSD0, SSD1, SSD2, SSD3)
	begin : SSD_SCAN_OUT
		case (ssdscan_clk) 
			2'b00: 
				SSD = SSD0;
			2'b01: 
				SSD = SSD1;
			2'b10: 
				SSD = SSD2;
			2'b11: 
				SSD = SSD3;				
		endcase 
	end	

	always @ (SSD) 
	begin : HEX_TO_SSD
		case (SSD)
			4'b0000: SSD_CATHODES = 7'b0000001 ; 4'b0001: SSD_CATHODES = 7'b1001111 ; 4'b0010: SSD_CATHODES = 7'b0010010 ; 4'b0011: SSD_CATHODES = 7'b0000110 ; 4'b0100: SSD_CATHODES = 7'b1001100 ; 4'b0101: SSD_CATHODES = 7'b0100100 ; 4'b0110: SSD_CATHODES = 7'b0100000 ; 4'b0111: SSD_CATHODES = 7'b0001111 ; 4'b1000: SSD_CATHODES = 7'b0000000 ; 4'b1001: SSD_CATHODES = 7'b0000100 ; 4'b1010: SSD_CATHODES = 7'b0001000 ; 4'b1011: SSD_CATHODES = 7'b1100000 ; 4'b1100: SSD_CATHODES = 7'b0110001 ; 4'b1101: SSD_CATHODES = 7'b1000010 ; 4'b1110: SSD_CATHODES = 7'b0110000 ; 4'b1111: SSD_CATHODES = 7'b0111000 ; endcase
	end	
endmodule
