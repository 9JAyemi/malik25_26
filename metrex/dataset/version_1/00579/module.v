
module latch_MEM_WB
	#(
	parameter B=32, W=5
	)
	(
	input wire clk,
	input wire reset,
	input wire ena,
	
	input wire [B-1:0] read_data_in,
	input wire [B-1:0] alu_result_in,
	input wire [W-1:0] mux_RegDst_in,
	
	output wire [B-1:0] read_data_out,
	output wire [B-1:0] alu_result_out,
	output wire [W-1:0] mux_RegDst_out,
	
	input wire wb_RegWrite_in,
	input wire wb_MemtoReg_in,
	
	output wire wb_RegWrite_out,
	output wire wb_MemtoReg_out

   );
	
	reg [B-1:0]read_data_reg;
	reg [B-1:0]alu_result_reg;
	reg [W-1:0]mux_RegDst_reg;
	
	reg wb_RegWrite_reg;
	reg wb_MemtoReg_reg;

	always @(posedge clk)
	begin
		if (reset)
		begin
			read_data_reg <= 0;
			alu_result_reg <= 0;
			mux_RegDst_reg <= 0;
			wb_RegWrite_reg <= 0;
			wb_MemtoReg_reg <= 0;
		end
		else
			if(ena==1'b1)
			begin
				
				read_data_reg <= read_data_in;
				alu_result_reg <= alu_result_in;
				mux_RegDst_reg <= mux_RegDst_in;
				
				wb_RegWrite_reg <= wb_RegWrite_in;
				wb_MemtoReg_reg <= wb_MemtoReg_in;
			end
	end
		
	assign read_data_out = read_data_reg;
	assign alu_result_out = alu_result_reg;
	assign mux_RegDst_out = mux_RegDst_reg;
	
	assign wb_RegWrite_out = wb_RegWrite_reg;
	assign wb_MemtoReg_out = wb_MemtoReg_reg;
endmodule
