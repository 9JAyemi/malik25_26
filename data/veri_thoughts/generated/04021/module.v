
module ClkDiv_5Hz(
		CLK,
		RST,
		CLKOUT
);

input            CLK;		input            RST;		output           CLKOUT;	reg CLKOUT;
	
   reg [23:0]       clkCount = 24'h000000;
   parameter [23:0] cntEndVal = 24'h989680;
   
always @(posedge CLK or posedge RST)
			
			if (RST == 1'b1) begin
					CLKOUT <= 1'b0;
					clkCount <= 24'h000000;
			end
			else begin
					if (clkCount == cntEndVal) begin
						CLKOUT <= (~CLKOUT);
						clkCount <= 24'h000000;
					end
					else begin
						clkCount <= clkCount + 1'b1;
					end
			end
   
endmodule
