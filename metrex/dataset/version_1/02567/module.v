`ifndef _REGISTER
`define _REGISTER

module register16(clk, out, in, write, reset);  output reg [15:0] out;
	input      [15:0] in;
	input      clk, write, reset;
	
	always@(posedge clk) begin
		if(reset==0) begin
			out = 16'b0;
		end
		else if(write == 1'b0) begin
			out = in;
		end
	end
	
endmodule


module register4(clk, out, in, write, reset);  output reg [3:0] out;
	input      [3:0] in;
	input      clk, write, reset;
	
	always@(posedge clk) begin
		if(reset==0) begin
			out = 4'b0;
		end
		else if(write == 1'b0) begin
			out = in;
		end
	end
	
endmodule

module register3(clk, out, in, write, reset);  output reg [2:0] out;
	input      [2:0] in;
	input      clk, write, reset;
	
	always@(posedge clk) begin
		if(reset==0) begin
			out = 3'b0;
		end
		else if(write == 1'b0) begin
			out = in;
		end
	end
	
endmodule


module register2(clk, out, in, write, reset);  output reg [1:0] out;
	input      [1:0] in;
	input      clk, write, reset;
	
	always@(posedge clk) begin
		if(reset==0) begin
			out = 2'b0;
		end
		else if(write == 1'b0) begin
			out = in;
		end
	end
	
endmodule


module register1(clk, out, in, write, reset);  output reg out;
	input      in;
	input      clk, write, reset;
	
	always@(posedge clk) begin
		if(reset==0) begin
			out = 1'b0;
		end
		else if(write == 1'b0) begin
			out = in;
		end
	end
	
endmodule

`endif
