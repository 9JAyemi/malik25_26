
module xor_system (
  input a,
  input b,
  output out
);

  wire not_a, not_b, not_a_b;

  not_gate not1(a, not_a);
  not_gate not2(b, not_b);
  not_gate not3(not_a_b, not_a_b);

  xor_gate xor1(a, not_b, not_a_b);
  xor_gate xor2(not_a, b, out);

endmodule

module not_gate (
  input in,
  output out
);

  assign out = ~in;

endmodule

module xor_gate (
  input a,
  input b,
  output out
);

  assign out = a ^ b;

endmodule
