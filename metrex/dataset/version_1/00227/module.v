`ifndef _MUX
`define _MUX

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

`endif
