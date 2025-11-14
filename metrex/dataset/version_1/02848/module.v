module Control_Unit(output reg done, Ld_AR_BR, Div_AR_x2_CR, Mul_BR_x2_CR, Clr_CR,
	input reset_b, start, AR_gt_0, AR_lt_0, clk);

	reg [1:0] state;

	always @(posedge clk) begin
		if (reset_b == 0) begin
			Ld_AR_BR = 0;
			Mul_BR_x2_CR = 0;
			Div_AR_x2_CR = 0;
			Clr_CR = 0;
			done = 0;
			state <= 2'b00;
		end else begin
			case (state)
				2'b00: begin
					Ld_AR_BR = 1;
					Mul_BR_x2_CR = 0;
					Div_AR_x2_CR = 0;
					Clr_CR = 0;
					done = 0;
					if (start) begin
						state <= 2'b01;
					end
				end
				2'b01: begin
					Ld_AR_BR = 0;
					Mul_BR_x2_CR = 0;
					Div_AR_x2_CR = 0;
					Clr_CR = 0;
					done = 1;
					if (AR_gt_0) begin
						state <= 2'b10;
					end else if (AR_lt_0) begin
						state <= 2'b11;
					end
				end
				2'b10: begin
					Ld_AR_BR = 0;
					Mul_BR_x2_CR = 1;
					Div_AR_x2_CR = 0;
					Clr_CR = 0;
					done = 1;
					state <= 2'b00;
				end
				2'b11: begin
					Ld_AR_BR = 0;
					Mul_BR_x2_CR = 0;
					Div_AR_x2_CR = 1;
					Clr_CR = 0;
					done = 1;
					state <= 2'b00;
				end
			endcase
		end
	end
	
endmodule