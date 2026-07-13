
module mux32bits_32to1 (
  input [4:0] s,
  input [31:0] i31,
  input [31:0] i30,
  input [31:0] i29,
  input [31:0] i28,
  input [31:0] i27,
  input [31:0] i26,
  input [31:0] i25,
  input [31:0] i24,
  input [31:0] i23,
  input [31:0] i22,
  input [31:0] i21,
  input [31:0] i20,
  input [31:0] i19,
  input [31:0] i18,
  input [31:0] i17,
  input [31:0] i16,
  input [31:0] i15,   
  input [31:0] i14,
  input [31:0] i13,
  input [31:0] i12,
  input [31:0] i11,
  input [31:0] i10,
  input [31:0] i9 ,
  input [31:0] i8 ,
  input [31:0] i7 ,
  input [31:0] i6 ,
  input [31:0] i5 ,
  input [31:0] i4 ,
  input [31:0] i3 ,
  input [31:0] i2 ,
  input [31:0] i1 ,
  input [31:0] i0 ,
  output reg [31:0] z
);

  always @(*) begin
    case (s)
      5'b00001: z <= i0;
      5'b00010: z <= i1;
      5'b00011: z <= i2;
      5'b00100: z <= i3;
      5'b00101: z <= i4;
      5'b00110: z <= i5;
      5'b00111: z <= i6;
      5'b01000: z <= i7;
      5'b01001: z <= i8;
      5'b01010: z <= i9;
      5'b01011: z <= i10;
      5'b01100: z <= i11;
      5'b01101: z <= i12;
      5'b01110: z <= i13;
      5'b01111: z <= i14;
      5'b10000: z <= i15;
      5'b10001: z <= i16;
      5'b10010: z <= i17;
      5'b10011: z <= i18;
      5'b10100: z <= i19;
      5'b10101: z <= i20;
      5'b10110: z <= i21;
      5'b10111: z <= i22;
      5'b11000: z <= i23;
      5'b11001: z <= i24;
      5'b11010: z <= i25;
      5'b11011: z <= i26;
      5'b11100: z <= i27;
      5'b11101: z <= i28;
      5'b11110: z <= i29;
      5'b11111: z <= i30;
      default:  z <= 0;
    endcase
  end

endmodule
