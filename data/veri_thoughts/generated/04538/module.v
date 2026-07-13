module logic_gates (
  input in1,
  input in2,
  output out_and,
  output out_or,
  output out_not,
  output out_xor,
  output out_xnor
);

  assign out_and = in1 & in2;
  assign out_or = in1 | in2;
  assign out_not = ~in1;
  assign out_xor = in1 ^ in2;
  assign out_xnor = ~(in1 ^ in2);

endmodule