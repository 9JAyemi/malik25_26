module mux2to1 (out, in0, in1, sel);
	output out;
	input in0, in1;
	input sel;
	assign out = sel ? in1 : in0;
endmodule

module or2 (out, in0, in1);
	output out;
	input in0, in1;
	assign out = in0 | in1;
endmodule

module mux4to1 (out, in0, in1, in2, in3, sel);
	output out;
	input in0, in1, in2, in3;
	input [1:0] sel;
	wire m0, m1, o;
	mux2to1 m2 (m0, in0, in1, sel[0]);
	mux2to1 m3 (m1, in2, in3, sel[0]);
	or2 o1 (o, m0, m1);
	mux2to1 m4 (out, m0, m1, sel[1]);
endmodule