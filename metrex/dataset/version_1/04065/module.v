module mutex_buffer #
(
	parameter integer C_BUFF_NUM = 4
) (
	input wire clk,
	input wire resetn,

	output wire wr_done,

	input wire                        w_sof,
	output reg [C_BUFF_NUM-1:0]       w_bmp,

	input wire                        r0_sof,
	output reg [C_BUFF_NUM-1:0]       r0_bmp,

	input wire                        r1_sof,
	output reg [C_BUFF_NUM-1:0]       r1_bmp
);

	assign wr_done = w_sof;

	reg [C_BUFF_NUM-1:0]	last_bmp;

	/// reader 0
	always @(posedge clk) begin
		if (resetn == 0) begin
			r0_bmp  <= 0;
		end
		else if (r0_sof) begin
			if (w_sof) begin
				r0_bmp  <= w_bmp;
			end
			else begin
				r0_bmp  <= last_bmp;
			end
		end
	end

	/// reader 1 (same as reader 0)
	always @(posedge clk) begin
		if (resetn == 0) begin
			r1_bmp  <= 0;
		end
		else if (r1_sof) begin
			if (w_sof) begin
				r1_bmp  <= w_bmp;
			end
			else begin
				r1_bmp  <= last_bmp;
			end
		end
	end

	/// last done (ready for read)
	always @(posedge clk) begin
		if (resetn == 0) begin
			last_bmp  <= {{C_BUFF_NUM-1{1'b0}}, 1'b1};
		end
		else if (w_sof) begin
			last_bmp  <= w_bmp;
		end
	end

	always @(posedge clk) begin
		if (resetn == 0) begin
			w_bmp  <= {{C_BUFF_NUM-1{1'b0}}, 1'b0};
		end
		else if (w_sof) begin
			casez (w_bmp | r0_bmp | r1_bmp)
			{{C_BUFF_NUM-1{1'b?}}, 1'b0}: begin
				w_bmp	<= {{C_BUFF_NUM-1{1'b0}}, 1'b1};
			end
			{{C_BUFF_NUM-2{1'b?}}, 1'b0, 1'b1}: begin
				w_bmp	<= {{C_BUFF_NUM-1{1'b0}}, 1'b0, 1'b1};
			end
			{{C_BUFF_NUM-3{1'b?}}, 1'b0, 1'b1, 1'b1}: begin
				w_bmp	<= {{C_BUFF_NUM-1{1'b0}}, 1'b0, 1'b0, 1'b1};
			end
			{{C_BUFF_NUM-4{1'b?}}, 1'b0, 1'b1, 1'b1, 1'b1}: begin
				w_bmp	<= {{C_BUFF_NUM-1{1'b0}}, 1'b0, 1'b0, 1'b0, 1'b1};
			end
			default: begin
				w_bmp  <= {{C_BUFF_NUM-1{1'b0}}, 1'b0};
			end
			endcase
		end
	end

endmodule