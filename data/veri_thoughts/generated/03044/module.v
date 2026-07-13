module mux2to1 (in0, in1, ctrl, out);
  input [3:0] in0;
  input [3:0] in1;
  input ctrl;
  output [3:0] out;

  assign out = (ctrl == 1'b0) ? in0 : in1;

endmodule