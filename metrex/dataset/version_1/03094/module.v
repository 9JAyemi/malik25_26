
module divider(

    input [7:0] div, input [7:0] dvr, input clk,
	 
    output [7:0] quotient, output [7:0] remainder );

integer i;
reg [7:0] diff; reg [7:0] qu;reg [7:0] rem;always @(posedge clk) begin

rem [7:0] = 8'b0; qu [7:0] = div[7:0]; for (i=0;i<=7;i=i+1) begin
rem = rem<<1;rem[0] = qu[7];qu = qu<<1;qu[0] = 1'b0;if ( rem >= dvr) begin
	
rem = rem-dvr;
qu[0] = 1'b1;

						end

	
			end
	
end 

assign remainder [7:0] = rem[7:0];
assign quotient [7:0] = qu[7:0];


endmodule
  