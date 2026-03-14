
module karnaugh_map(
  input wire A, B, C,
  output wire F
);

  // Minimized Boolean expression: F = A'B' + AB' + BC
  assign F = (~A & ~B) | (A & ~B) | (B & C);

endmodule
