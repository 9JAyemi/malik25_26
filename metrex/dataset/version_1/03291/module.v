module reg_read(in, readAdd1, readAdd2, regValue1, regValue2, equalValue, write, writeAdd, writeR7, inR7, clk, reset);

	output [15:0] regValue1, regValue2;
	output 	      equalValue;
	input  [15:0] in, inR7;
	input  [2:0]  readAdd1, readAdd2, writeAdd;
	input	      write, writeR7, clk, reset;
	
	register_file rfile(.clk(clk), .out1(regValue1), .out2(regValue2), .readAdd1(readAdd1), .readAdd2(readAdd2), .write(write), .writeAdd(writeAdd), .writeR7(writeR7), .inR7(inR7), .in(in), .reset(reset));
	equal eqCheck(.in1(regValue1), .in2(regValue2), .out(equalValue));

endmodule

module register_file(clk, out1, out2, readAdd1, readAdd2, write, writeAdd, writeR7, inR7, in, reset); output [15:0] out1, out2;
	input  [15:0] in, inR7;
	input  [2:0]  readAdd1, readAdd2, writeAdd;
	input         write, clk, reset, writeR7;
	
	wire   [15:0] data0,  data1,  data2,  data3,  data4,  data5,  data6,  data7;
	wire   [7:0]  writeLinesInit, writeLines;
	
	decode8 dem(writeAdd, writeLinesInit);
	mux16x8 mux1(data0, data1, data2, data3, data4, data5, data6, data7, readAdd1, out1);
	mux16x8 mux2(data0, data1, data2, data3, data4, data5, data6, data7, readAdd2, out2);
	
	or a0(writeLines[0], write, ~writeLinesInit[0]);
	or a1(writeLines[1], write, ~writeLinesInit[1]);
	or a2(writeLines[2], write, ~writeLinesInit[2]);
	or a3(writeLines[3], write, ~writeLinesInit[3]);
	or a4(writeLines[4], write, ~writeLinesInit[4]);
	or a5(writeLines[5], write, ~writeLinesInit[5]);
	or a6(writeLines[6], write, ~writeLinesInit[6]);
	or a7(writeLines[7], writeR7, ~writeLinesInit[7]);
	
	register16 r0(clk, data0, in, writeLines[0], reset);
	register16 r1(clk, data1, in, writeLines[1], reset);
	register16 r2(clk, data2, in, writeLines[2], reset);
	register16 r3(clk, data3, in, writeLines[3], reset);
	register16 r4(clk, data4, in, writeLines[4], reset);
	register16 r5(clk, data5, in, writeLines[5], reset);
	register16 r6(clk, data6, in, writeLines[6], reset);
	register16 r7(clk, data7, inR7, writeLines[7], reset);
	endmodule

module equal(in1, in2, out);
	
	output out;
	input [15:0] in1, in2;
	
	assign out = (in1==in2);
	
endmodule

module decode8(selectInput, out);  output reg [7:0] out;
	input  [2:0] selectInput;
	
	always@(selectInput) begin
		case(selectInput)
			0: out = 8'b00000001;
			1: out = 8'b00000010;
			2: out = 8'b00000100;
			3: out = 8'b00001000;
			4: out = 8'b00010000;
			5: out = 8'b00100000;
			6: out = 8'b01000000;
			7: out = 8'b10000000;
		endcase
	end
	
endmodule

module mux16x8(data0, data1, data2, data3, data4, data5, data6, data7, selectInput, out);  output reg [15:0] out;
	input  [15:0] data0, data1, data2, data3, data4, data5, data6, data7;
	input  [2:0] selectInput;
	
	always@(data0 or data1 or data2 or data3 or data4 or data5 or data6 or data7 or selectInput) begin
		case(selectInput)
			0: out = data0;
			1: out = data1;
			2: out = data2;
			3: out = data3;
			4: out = data4;
			5: out = data5;
			6: out = data6;
			7: out = data7;
		endcase
	end
	
endmodule


module mux16x4(data0, data1, data2, data3, selectInput, out);  output reg [15:0] out;
	input  [15:0] data0, data1, data2, data3;
	input  [1:0] selectInput;
	
	always@(data0 or data1 or data2 or data3 or selectInput) begin
		case(selectInput)
			0: out = data0;
			1: out = data1;
			2: out = data2;
			3: out = data3;
		endcase
	end
	
endmodule


module mux16x2(data0, data1, selectInput, out);  output reg [15:0] out;
	input  [15:0] data0, data1;
	input  selectInput;
	
	always@(data0 or data1 or selectInput) begin
		case(selectInput)
			0: out = data0;
			1: out = data1;
		endcase
	end
	
endmodule

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