module MEM(
	input clk,
	input [5:0] Op,
	input [2:0] Condition,
	input Branch,
	input MemWrite,
	input RegWrite,
	input [31:0] MemData,
	input Less,Zero,Overflow,
	input [31:0] WBData,
	output [31:0] MemData_Mem,
	output [3:0] Rd_write_byte_en,
	output RegWriteValid,
	output BranchValid,
	output [3:0]Mem_write_byte_en
);
wire [31:0] Mem_data_in;
wire [31:0] Mem_data_out;
ConditionCheck ConditionCheck(Condition,Branch,RegWrite,Less,Zero,Overflow,BranchValid,RegWriteValid);
reg_shifter reg_shifter(MemData,WBData[1:0],MemWrite,Op,Mem_data_in,Mem_write_byte_en);
Mem Mem(Mem_write_byte_en,clk,Mem_data_in,WBData,Mem_data_out);
mem_shifter mem_shifter(Mem_data_out,WBData[1:0],Op,MemData_Mem,Rd_write_byte_en);
endmodule

module ConditionCheck(
	input [2:0] Condition,
	input Branch,
	input RegWrite,
	input Less,Zero,Overflow,
	output reg BranchValid,RegWriteValid
);

always @(*)
begin
if(Branch==0)
BranchValid=0;
else
begin
case(Condition)
3'b000:
BranchValid=0;
3'b001:
BranchValid=Zero;
3'b010:
BranchValid=~Zero;
3'b011:
BranchValid=Less|Zero;3'b100:
BranchValid=Less;3'b101:
BranchValid=~Less;3'b110:
BranchValid=~(Less|Zero);3'b111:
BranchValid=0;
endcase
end

if(RegWrite==0)
RegWriteValid=0;
else if(Overflow==1)
RegWriteValid=0;
else
RegWriteValid=1;
end
endmodule
module reg_shifter(
	input [31:0] rt_out,
	input	[1:0] mem_addr_in,
	input	MemWrite,
	input [5:0] IR_out,
	output reg [31:0] rt_out_shift,
	output reg [3:0] mem_byte_write_out
);
reg [3:0]mem_byte_write;
always @ (*)
begin
	if (IR_out == 6'b101011) begin rt_out_shift = rt_out;mem_byte_write=4'b1111;end
	else begin
		case (mem_addr_in)
			2'b00: begin rt_out_shift = {rt_out[7:0],  24'b0};mem_byte_write=4'b1000;end
			2'b01: begin rt_out_shift = {rt_out[15:0], 16'b0};mem_byte_write=4'b1100;end
			2'b10: begin rt_out_shift = {rt_out[23:0], 8'b0};mem_byte_write=4'b1110;end
			2'b11: begin rt_out_shift = rt_out;mem_byte_write=4'b1111;end
		endcase
	end
	mem_byte_write_out = mem_byte_write & {4{MemWrite}};
end

endmodule




module mem_shifter(
	input [31:0] mem_data_out,
	input	[1:0] mem_addr_in,
	input [5:0] IR_out,
	output reg [31:0] mem_data_shift,
	output reg [3:0] Rd_write_byte_en
);

always @ (*)
begin
	if (IR_out == 6'b100011)begin
		mem_data_shift = mem_data_out;
		Rd_write_byte_en=4'b1111;
	end
	else begin
		case (mem_addr_in)
			2'b00: begin mem_data_shift = mem_data_out; Rd_write_byte_en=4'b1111;end
			2'b01: begin mem_data_shift = {mem_data_out[23:0], 8'b0};Rd_write_byte_en=4'b1110; end
			2'b10: begin mem_data_shift = {mem_data_out[15:0], 16'b0};Rd_write_byte_en=4'b1100; end
			2'b11: begin mem_data_shift = {mem_data_out[7:0],  24'b0};Rd_write_byte_en=4'b1000; end
		endcase
	end
end

endmodule

module Mem(
	input [3:0]Mem_byte_wr_in,
	input clk,
	input [31:0]Mem_data,
	input [31:0]Mem_addr_in,
	output reg [31:0]Mem_data_out
);
reg [31:0]addr;
integer i;
reg [7:0] IR_reg [500:0];
initial
begin
for(i=0;i<=500;i=i+1) IR_reg[i]=8'b0;
IR_reg[256] = 8'b10011000;
IR_reg[257] = 8'b10010110;
IR_reg[258] = 8'b10011100;
IR_reg[259] = 8'b11001110;
end
always@(posedge clk)
begin
addr = {Mem_addr_in[31:2],2'b00};
if(Mem_byte_wr_in[3])
	IR_reg[addr+3]<=Mem_data[31:24];
if(Mem_byte_wr_in[2])
	IR_reg[addr+2]<=Mem_data[23:16];
if(Mem_byte_wr_in[1])
	IR_reg[addr+1]<=Mem_data[15:8];
if(Mem_byte_wr_in[0])
	IR_reg[addr]<=Mem_data[7:0];
if(addr >= 496)
		Mem_data_out <= 32'h00000000;
else begin
	Mem_data_out[31:24]<=IR_reg[addr + 3];
	Mem_data_out[23:16]<=IR_reg[addr+2];
	Mem_data_out[15:8]<=IR_reg[addr+1];
	Mem_data_out[7:0]<=IR_reg[addr];
end
end
endmodule


