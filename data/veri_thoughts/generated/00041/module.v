module karnaugh_map(
  input wire A, B, C, D,
  output reg F
);

  // Parameter declarations, if needed

  // Verilog code to implement the Karnaugh map expression for F
  always @* begin
    F = (A & ~B & C & ~D) | (~A & B & ~C & D) | (A & ~B & ~C & D) | (~A & B & C & ~D);
  end

endmodule