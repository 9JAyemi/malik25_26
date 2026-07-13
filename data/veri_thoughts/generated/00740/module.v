module mux2to1 (
  in1, // input 1
  in2, // input 2
  sel, // select input
  out // output
);

	input in1, in2, sel;
	output out;

	assign out = sel ? in2 : in1;

endmodule