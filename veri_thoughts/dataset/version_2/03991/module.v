module mux4
	#(parameter width=16)
	(input [width-1:0] in0,
	 input [width-1:0] in1,
	 input [width-1:0] in2,
	 input [width-1:0] in3,
	 input [1:0] sel,
	 output [width-1:0] out);

	assign out = (sel == 2'b00) ? in0 :
	             (sel == 2'b01) ? in1 :
	             (sel == 2'b10) ? in2 :
	             (sel == 2'b11) ? in3 :
	             16'b0;
endmodule