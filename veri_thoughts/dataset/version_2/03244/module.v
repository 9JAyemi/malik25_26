module karnaugh_map(
  input wire A, B, C, D,
  output reg F
);

  always @* begin
    case ({A,B})
      2'b00: F = D ^ C;
      2'b01: F = B ^ C;
      2'b11: F = C ^ D;
      2'b10: F = A ^ D;
    endcase
  end

endmodule