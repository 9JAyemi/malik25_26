module karnaugh_map(
  input wire A, B, C,
  output reg F
);

  always @* begin
    case ({A,B,C})
      3'b000, 3'b011: F = 1'b1;
      3'b100, 3'b111: F = 1'b0;
      default: F = 1'b0;
    endcase
  end

endmodule