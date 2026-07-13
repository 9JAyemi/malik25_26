module xor2 (
  input wire a,
  input wire b,
  output wire y
);
  assign y = a ^ b;
endmodule
module xor3 (
  input wire a,
  input wire b,
  input wire c,
  output wire y
);
  wire temp1, temp2;
  xor2 u1 (.a(a), .b(b), .y(temp1));
  xor2 u2 (.a(temp1), .b(c), .y(temp2));
  assign y = temp2;
endmodule
