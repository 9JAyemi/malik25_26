
module FSM(
    input [31:0] x,					input [31:0] y,					input [31:0] z,					input [31:0] k,					input [31:0] kappa_LUTRot, 
	 input [31:0] theta_LUTRot, 
	 input [31:0] delta_LUTRot,
	 input [31:0] kappa_LUTVec, 
	 input [31:0] theta_LUTVec, 
	 input [31:0] delta_LUTVec,
    input [31:0] theta_LUT,		input [31:0] kappa_LUT,		input [31:0] delta_LUT,		input [1:0] mode,				input operation,					input clock,
	 input done_LUTRot,
	 input done_LUTVec,
	 input done_LUT,					output reg enable_LUT,			output reg [7:0] address,		output reg [31:0] theta_out,	output reg [31:0] kappa_out,	output reg [31:0] delta_out,	output reg done_FSM,
	 output reg [31:0] x_final,
	 output reg [31:0] y_final,
	 output reg [31:0] z_final,
	 output reg [31:0] k_final,
	 input done_ALU
    );

reg [7:0] exponent;
reg converge;

always @ (*)
begin
	
	if (operation == 1'b1)	
	begin
		exponent <= 8'b01111111 - z[30:23];
	end
	
	else if (operation == 1'b0)
	begin
		exponent <= x[30:23] - y[30:23];
	end
	

end

always @ (posedge clock)
begin
	
		if ((done_LUT == 1'b1 || done_LUTRot == 1'b1 || done_LUTVec == 1'b1) && enable_LUT == 1'b1)
	begin
		
		if ((operation == 1'b0) && (mode == 2'b00 || (exponent <= 8'b11110011 && exponent > 8'b10000000)))
		begin
			delta_out <= delta_LUT;
			delta_out[30:23] <= exponent + 8'b01111111;
			theta_out <= theta_LUT;
			theta_out[30:23] <= exponent + 8'b01111111;
			enable_LUT <= 1'b0;
			done_FSM <= 1'b1;
		end
		
		else if (operation == 1'b1)
		begin
			theta_out[31] <= ~z[31];
			delta_out[31] <= ~z[31];
			theta_out[30:0] <= theta_LUTRot[30:0];
			delta_out[30:0] <= delta_LUTRot[30:0];
			kappa_out <= kappa_LUTRot;
			enable_LUT <= 1'b0;
			done_FSM <= 1'b1;
		end
		
		else
		begin
			theta_out <= theta_LUTVec;
			delta_out <= delta_LUTVec;
			kappa_out <= kappa_LUTVec;
			enable_LUT <= 1'b0;
			done_FSM <= 1'b1;
		end
		
	end
	
	if (done_ALU == 1'b1)
	begin
		done_FSM <= 1'b0;
	end
	
	if (operation == 1'b1)												
	begin
		
		if (z[30:23] <= 8'b01110000)
		begin
			converge <= 1'b1;
			x_final <= x;
			y_final <= y;
			z_final <= z;
			k_final <= k;
		end
		
		else if (mode == 2'b00)												
		begin
			theta_out[30:0] <= z[30:0];
			delta_out[30:0] <= z[30:0];
			theta_out[31]	<= ~z[31];
			delta_out[31]	<= ~z[31];
			kappa_out <= 32'h3F800000;
			done_FSM <= 1'b1;
		end
		
		else if (mode == 2'b11 && z[30:23] >= 8'b01111111)
		begin
			theta_out <= 32'hBF800000;
			delta_out <= 32'hBF42F7D6;
			kappa_out <= 32'h3FC583AB;
			done_FSM <= 1'b1;
		end
		
		else if (mode == 2'b01 && z[30:23] >= 8'b01111111)		
		begin
			theta_out <= 32'hBF800000;
			delta_out <= 32'hBFC75923;
			kappa_out <= 32'h3FECE788;
			done_FSM <= 1'b1;
		end
	
		else if (mode != 2'b00 && z[30:23] < 8'b01111111 && z[30:23] > 8'b01110011) 			
		begin
			address[7:4] <= exponent[3:0];
			address[3:0] <= z[22:19];
			enable_LUT <= 1'b1;
		end	
		
		else if (mode != 2'b00 && z[30:23] <= 8'b01110011)												
		begin
			theta_out[30:0] <= z[30:0];
			delta_out[30:0] <= z[30:0];
			theta_out[31]	<= ~z[31];
			delta_out[31]	<= ~z[31];
			kappa_out <= 32'h3F800000;
			done_FSM <= 1'b1;
		end
		
	end
	
	else if (operation == 1'b0)					
	begin
		
		if (z[30:23] <= 8'b01110000)
		begin
			converge <= 1'b1;
		end
		
		else if (mode == 2'b00)
		begin
			address[7:4] <= x[22:19];
			address[3:0] <= y[22:19];
			kappa_out <= 32'h3F8;
			enable_LUT <= 1'b1;
		end
		
		else if (mode != 2'b00 && exponent > 8'b11110011 && exponent <= 8'b11111111) 	
		begin
			address[7:4] <= exponent[3:0];
			address[3:2] <= x[22:21];
			address[1:0] <= y[22:21];
			enable_LUT <= 1'b1;
		end	
		
		else if (mode != 2'b00 && exponent <= 8'b11110011 && exponent > 8'b10000000)
		begin
			address[7:4] <= x[22:19];
			address[3:0] <= y[22:19];
			kappa_out <= 32'h3F8;
			enable_LUT <= 1'b1;
		end
		
		else if (mode == 2'b11 && exponent <= 8'b10000000)
		begin
			delta_out <= 32'h3F733333;
			theta_out <= 32'h3FEA77CB;
			kappa_out <= 32'h3E9FDF38;				done_FSM <= 1'b1;
		end
				
		else if (mode == 2'b01 && exponent <= 8'b10000000)
		begin
			delta_out <= 32'h3F8;					theta_out <= 32'h3F490FDB;
			kappa_out <= 32'h3FB504F4;
			done_FSM <= 1'b1;
		end
		
	end
	
end
endmodule
