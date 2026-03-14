module FORWARD(
input [4:0] Rs_ID_EX,
input [4:0] Rt_ID_EX,
input [4:0] Rd_EX_MEM,
input [4:0] Rs_IF_ID,
input [4:0] Rt_IF_ID,
input [4:0] Rd_MEM_REG,
input RegWrite_EX_MEM,
input RegWrite_MEM_REG,
input [3:0] Rd_write_byte_en,
input loaduse,
output reg [3:0] RsOut_sel,
output reg [3:0] RtOut_sel,
output reg [7:0] A_in_sel,
output reg [7:0] B_in_sel
);
always@(*)begin
	if(!loaduse && RegWrite_MEM_REG && Rd_MEM_REG == Rs_IF_ID)RsOut_sel = Rd_write_byte_en;
	else 
		RsOut_sel = 4'b0000;
		
	if(!loaduse && RegWrite_MEM_REG && Rd_MEM_REG == Rt_IF_ID)RtOut_sel = Rd_write_byte_en;
	else 
		RtOut_sel = 4'b0000;
		
	if(RegWrite_EX_MEM  && Rd_EX_MEM == Rs_ID_EX)A_in_sel = 8'b01010101;
	else if(RegWrite_MEM_REG && Rd_MEM_REG == Rs_ID_EX)begin 
			if(Rd_write_byte_en[3])
				A_in_sel[7:6] = 2'b10;
			else
				A_in_sel[7:6] = 2'b00;
			if(Rd_write_byte_en[2])
				A_in_sel[5:4] = 2'b10;
			else
				A_in_sel[5:4] = 2'b00;
			if(Rd_write_byte_en[1])
				A_in_sel[3:2] = 2'b10;
			else
				A_in_sel[3:2] = 2'b00;
			if(Rd_write_byte_en[0])
				A_in_sel[1:0] = 2'b10;
			else
				A_in_sel[1:0] = 2'b10;
		end
	else 
		A_in_sel = 8'b00000000;
	if(RegWrite_EX_MEM && Rd_EX_MEM == Rt_ID_EX)B_in_sel = 8'b01010101;
	else if(RegWrite_MEM_REG && Rd_MEM_REG == Rt_ID_EX)begin 
			if(Rd_write_byte_en[3])
				B_in_sel[7:6] = 2'b10;
			else
				B_in_sel[7:6] = 2'b00;
			if(Rd_write_byte_en[2])
				B_in_sel[5:4] = 2'b10;
			else
				B_in_sel[5:4] = 2'b00;
			if(Rd_write_byte_en[1])
				B_in_sel[3:2] = 2'b10;
			else
				B_in_sel[3:2] = 2'b00;
			if(Rd_write_byte_en[0])
				B_in_sel[1:0] = 2'b10;
			else
				B_in_sel[1:0] = 2'b00;
		end
	else 
		B_in_sel = 8'b000000000;
	
end
endmodule