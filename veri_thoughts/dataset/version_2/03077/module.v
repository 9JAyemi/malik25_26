
module and_or_gate (
  input in1,
  input in2,
  output out
);

  wire and_out;
  wire inv_and_out;

  and_gate and_gate_inst (
    .in1(in1),
    .in2(in2),
    .out(and_out)
  );

  not_gate not_gate_inst (
    .in(and_out),
    .out(inv_and_out)
  );

  or_gate or_gate_inst (
    .in1(and_out),
    .in2(inv_and_out),
    .out(out)
  );

endmodule
module and_gate (
  input in1,
  input in2,
  output out
);

  wire and1_out;
  wire and2_out;

  buf_2_gate and1_inst (
    .in1(in1),
    .in2(in2),
    .out(and1_out)
  );

  not_gate and2_inst (
    .in(and1_out),
    .out(out)
  );

endmodule
module or_gate (
  input in1,
  input in2,
  output out
);

  buf_2_gate or_inst (
    .in1(in1),
    .in2(in2),
    .out(out)
  );

endmodule
module not_gate (
  input in,
  output out
);

  buf_2_gate not_inst (
    .in1(in),
    .in2(1'b0),
    .out(out)
  );

endmodule
module buf_2_gate (
  input in1,
  input in2,
  output out
);

  assign out = in1 | in2;

endmodule