
module RCB_FRL_LED_Clock(Test_Clock_in, LED_Clock_out, RST);
    input Test_Clock_in;
    output LED_Clock_out;
    input RST;

	reg[9:0] count1;
	reg[9:0] count2;
	reg[9:0] count3;
	reg LED_Clock_out_reg;
	
	assign LED_Clock_out = LED_Clock_out_reg;

always @(posedge Test_Clock_in or posedge RST) begin
	if (RST) begin
		count1 <= 1'b0;
		count2 <= 1'b0;
		count3 <= 1'b0;
		LED_Clock_out_reg <= 1'b0;
		end
	else begin
		if (count3 < 448) begin
			if (count2 < 1000) begin
				if (count1 < 1000) 
					count1 <= count1 + 1'b1;
				else
					begin
						count1 <= 1'b0;
						count2 <= count2 + 1'b1;
					end
				end
			else
				begin
					count2 <= 1'b0;
					count3 <= count3 + 1'b1;
				end
			end
		else				
			begin
				count3 <= 1'b0;
				LED_Clock_out_reg <= ~LED_Clock_out_reg;
			end
		end
	end

endmodule

module RCB_FRL_LED_Clock_DIV(Test_Clock_in, LED_Clock_out, RST);
    input Test_Clock_in;
    output LED_Clock_out;
    input RST;

	reg[9:0] count1;
	reg[9:0] count2;
	reg[9:0] count3;
	reg LED_Clock_out_reg;
	
	assign LED_Clock_out = LED_Clock_out_reg;

always @(posedge Test_Clock_in or posedge RST) begin
	if (RST) begin
		count1 <= 1'b0;
		count2 <= 1'b0;
		count3 <= 1'b0;
		LED_Clock_out_reg <= 1'b0;
		end
	else begin
		if (count3 < 56) begin
			if (count2 < 1000) begin
				if (count1 < 1000) 
					count1 <= count1 + 1'b1;
				else
					begin
						count1 <= 1'b0;
						count2 <= count2 + 1'b1;
					end
				end
			else
				begin
					count2 <= 1'b0;
					count3 <= count3 + 1'b1;
				end
			end
		else				
			begin
				count3 <= 1'b0;
				LED_Clock_out_reg <= ~LED_Clock_out_reg;
			end
		end
	end

endmodule
