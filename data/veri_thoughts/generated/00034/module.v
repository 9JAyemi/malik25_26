
module karnaugh_map(
  input wire A, B, C, D,
  output wire F
);

  // Simplified Boolean expression
  assign F = !A && (B || C);

endmodule