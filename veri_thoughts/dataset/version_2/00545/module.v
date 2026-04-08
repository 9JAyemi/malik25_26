
module BIN_DEC2(

	input [15:0] B2,
	output reg [19:0] bcdout2
	);
	
	reg [35:0] z;
	integer i;

always @(*)
  begin
    for(i = 0; i <= 35; i = i+1)
	z[i] = 0;
    z[18:3] = B2; repeat(13)
	 begin
	if(z[19:16] > 4)	
		z[19:16] = z[19:16] + 3;
	if(z[23:20] > 4) 	
		z[23:20] = z[23:20] + 3;
	if(z[27:24] > 4) 	
		z[27:24] = z[27:24] + 3;
	if(z[31:28] > 4) 	
		z[31:28] = z[31:28] + 3;
	if(z[35:32] > 4) 	
		z[35:32] = z[35:32] + 3;

	z[35:1] = z[34:0];
	
	end      
    bcdout2 = z[35:16];end         
  
endmodule