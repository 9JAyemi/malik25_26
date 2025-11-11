module umult8(reg_A, reg_B, result);
	input [0:7] reg_A, reg_B;
	
	output [0:15] result;
	
	reg [0:15] p8a_0;
	reg [0:15] p8b_0;
	reg [0:15] pt;
	reg [0:15] result;
	
	integer i;

	always @ (reg_A or reg_B)
		begin
		p8a_0=16'b0;
		p8b_0=16'b0;
		pt=16'b0;
		
		
		p8b_0={{8{1'b0}},reg_B[0:7]};
		
		p8a_0={{8{1'b0}},reg_A[0:7]};

		
		for (i=15; i>7; i=i-1)
			begin
			pt=pt+(p8a_0[i]?(p8b_0<<(8'd15-i)):16'b0);
			end
		result<=pt;
		end
endmodule
