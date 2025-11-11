module FIFO_WxD #(
	parameter U_FIFO_WIDTH = 24, 	// word width of FIFO
	parameter U_FIFO_SQ_DEPTH = 10 // 2^n depth of the FIFO (3k byte - 1 FIFO by default)
	)(
	input wire rst,
	input wire [U_FIFO_WIDTH - 1:0] dataIn,
	input wire wr_en,
	input wire rd_en,
	output wire [U_FIFO_WIDTH - 1:0] dataOut,
	output wire full_flg,
	output wire empty_flg
	);

	// FIFO buffer instance
	reg [U_FIFO_WIDTH - 1:0] fifo [(2**U_FIFO_SQ_DEPTH) - 1:0];
	
	// pointer counters (set to 0 initially)
	reg [U_FIFO_SQ_DEPTH - 1:0] wr_ptr = 0;
	reg [U_FIFO_SQ_DEPTH - 1:0] rd_ptr = 0;
	
	// write block
	always@(posedge wr_en or negedge rst)
	begin
		
		if(!rst)	// async reset
			wr_ptr <= 0;
		else if(!full_flg) // write data to the buffer and inc the write pointer
		begin
			fifo[wr_ptr] <= dataIn;
			wr_ptr <= wr_ptr + 1'b1;
		end
	end // write block

	// read block
	always@(posedge rd_en or negedge rst)
	begin
		
		if(!rst)
			rd_ptr <= 0;
		else if(!empty_flg)
		begin
			rd_ptr <= rd_ptr + 1'b1;
		end
	end // read block

	// assign the outputs continously (pointers determine flags and data)
	assign empty_flg = (wr_ptr == rd_ptr)? 1'b1 : 1'b0; 
	assign full_flg = ((wr_ptr + {{U_FIFO_SQ_DEPTH-1{1'b0}}, 1'b1}) == rd_ptr)? 1'b1 : 1'b0; // because of the full flg decision the fifo depth is 2^n - 1
	assign dataOut = (empty_flg)? {U_FIFO_WIDTH{1'b0}} : fifo[rd_ptr]; // 0 if empty
	
endmodule