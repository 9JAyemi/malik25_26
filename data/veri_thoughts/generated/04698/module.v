module not_gate (
  input wire in,
  output wire out
);

  assign out = ~in;

endmodule
module and_gate (
  input wire a,
  input wire b,
  output wire out
);

  assign out = a & b;

endmodule
module or_gate (
  input wire a,
  input wire b,
  output wire out
);

  assign out = a | b;

endmodule
module xor_gate (
  input wire a,
  input wire b,
  output wire out
);

  wire n1, n2, n3, n4;

  not_gate n(
    .in(a),
    .out(n1)
  );

  not_gate n_(
    .in(b),
    .out(n2)
  );

  and_gate a1(
    .a(a),
    .b(n2),
    .out(n3)
  );

  and_gate a2(
    .a(n1),
    .b(b),
    .out(n4)
  );

  or_gate o(
    .a(n3),
    .b(n4),
    .out(out)
  );

endmodule
