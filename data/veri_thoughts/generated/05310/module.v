module Multiplexer_4to1 (
    input ctrl0, ctrl1,
    input [0:0] D0, D1, D2, D3,
    output reg [0:0] S
);

  always @* begin
    case ({ctrl1, ctrl0})
      2'b00: S = D0;
      2'b01: S = D1;
      2'b10: S = D2;
      2'b11: S = D3;
    endcase
  end

endmodule

module LUT4 (
    input [3:0] I,
    output reg O
);

  always @* begin
    case (I)
      4'b0000: O = 1'b1;
      4'b0001: O = 1'b0;
      4'b0010: O = 1'b1;
      4'b0011: O = 1'b0;
      4'b0100: O = 1'b1;
      4'b0101: O = 1'b0;
      4'b0110: O = 1'b1;
      4'b0111: O = 1'b0;
      4'b1000: O = 1'b0;
      4'b1001: O = 1'b1;
      4'b1010: O = 1'b0;
      4'b1011: O = 1'b1;
      4'b1100: O = 1'b0;
      4'b1101: O = 1'b1;
      4'b1110: O = 1'b0;
      4'b1111: O = 1'b1;
    endcase
  end

endmodule