
module Stack(input clk, rst, input [1:0] stackCntrl, input [11:0] pushValue, output reg [11:0] popValue);
	reg [2:0] stackPntr;
	reg [11:0] data [0:7];
	
	always @ (posedge clk, posedge rst) begin
		if (rst) begin
			stackPntr <= 3'b000;
			data[0] <= 12'd0;
			data[1] <= 12'd0;
			data[2] <= 12'd0;
			data[3] <= 12'd0;
			data[4] <= 12'd0;
			data[5] <= 12'd0;
			data[6] <= 12'd0;
			data[7] <= 12'd0;
		end
		else begin
			if (stackCntrl == 2'b01) begin // push
				if (stackPntr < 3'b111) begin
					data[stackPntr] <= pushValue + 12'd1;
					stackPntr <= stackPntr + 1;
				end
			end
			else if (stackCntrl == 2'b10) begin // pop
				if (stackPntr > 3'b000) begin
					stackPntr <= stackPntr - 1;
					popValue <= data[stackPntr];
				end
			end
		end
	end
endmodule