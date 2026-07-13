
module BCD_to_Binary (
  input [3:0] bcd,
  output reg [7:0] bin
);

  always @(*) begin
    case(bcd)
      4'b0000: bin = 8'b00000000;
      4'b0001: bin = 8'b00000001;
      4'b0010: bin = 8'b00000010;
      4'b0011: bin = 8'b00000011;
      4'b0100: bin = 8'b00000100;
      4'b0101: bin = 8'b00000101;
      4'b0110: bin = 8'b00000110;
      4'b0111: bin = 8'b00000111;
      4'b1000: bin = 8'b00001000;
      4'b1001: bin = 8'b00001001;
      default: bin = 8'b11111111; // The default case should output all 1s (binary 255) to indicate an error.
    endcase
  end

endmodule