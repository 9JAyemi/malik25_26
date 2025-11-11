

module AGrises (
	input clk,
	input rst,

	output [DATA_WIDTH-1:0] data_fifo_out,
	output data_valid_fifo_out,
	input wire [FIFO_DEPTH_LOG2:0] usedw_fifo_out,
	
	input wire [DATA_WIDTH-1:0] data_fifo_in,
	output read_fifo_in,
	input wire [FIFO_DEPTH_LOG2:0] usedw_fifo_in,

	input start,
	output endf
);
   
	parameter DATA_WIDTH=32;
	parameter FIFO_DEPTH = 256;
	parameter FIFO_DEPTH_LOG2 = 8;
	
	reg [1:0] stages;
	wire stages_init;
	reg [1:0] run;
	
	reg [14:0] grey_aux;
	reg [7:0] grey;
	
	reg [18:0] pixel_counter;
	
	always @ (posedge clk or posedge rst) begin
		if (rst == 1) begin
			run <= 0;
		end else begin
			if (start == 1) begin
				run <= 1;
			end else begin
				if (pixel_counter == 0) begin
					run <= 2;
				end
				if (endf == 1) begin
					run <= 0;
				end
			end
		end
	end
	
	always @ (posedge clk) begin
		if (start == 1) begin
			pixel_counter <= 384000;
		end else begin
			if (data_valid_fifo_out) begin
				pixel_counter <= pixel_counter - 1;
			end
		end
	end
	
	always @ (posedge clk) begin
      if (start == 1) begin
			stages <= 0;
		end else begin
			if (stages_init == 1) begin
				stages <= 1;
				grey_aux = data_fifo_in[23:16]*8'd30 + data_fifo_in[15:8]*8'd59 + data_fifo_in[7:0]*8'd11;
				grey = 8'd2 * grey_aux[14:8];
				grey = grey + (grey_aux[14:8] / 8'd2);
			end else begin
				if (stages == 1) begin
					stages <= 2;
					grey = grey + (grey_aux[14:8] / 8'd19);
					grey = grey + (grey_aux[7:0] / 8'd64);
				end else begin
					if (stages == 2) begin
						stages <= 0;
					end
				end
			end
		end
	end
	
	assign stages_init = ((usedw_fifo_in > 32)|(pixel_counter < 33)) & (usedw_fifo_out < FIFO_DEPTH) & (run == 1) & (stages == 0);

	assign read_fifo_in = (run == 1) & (stages == 1);

	assign data_fifo_out = {8'd0,{3{grey}}};
	assign data_valid_fifo_out = (run == 1) & (stages == 2);
	
	assign endf = (run == 2);
	
endmodule
