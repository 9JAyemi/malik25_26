module mux32bits_32to1_sva (
  input logic clk,                 // Sampling clock for assertions (RTL has no clock)
  input logic [4:0] s,
  input logic [31:0] i31,
  input logic [31:0] i30,
  input logic [31:0] i29,
  input logic [31:0] i28,
  input logic [31:0] i27,
  input logic [31:0] i26,
  input logic [31:0] i25,
  input logic [31:0] i24,
  input logic [31:0] i23,
  input logic [31:0] i22,
  input logic [31:0] i21,
  input logic [31:0] i20,
  input logic [31:0] i19,
  input logic [31:0] i18,
  input logic [31:0] i17,
  input logic [31:0] i16,
  input logic [31:0] i15,
  input logic [31:0] i14,
  input logic [31:0] i13,
  input logic [31:0] i12,
  input logic [31:0] i11,
  input logic [31:0] i10,
  input logic [31:0] i9,
  input logic [31:0] i8,
  input logic [31:0] i7,
  input logic [31:0] i6,
  input logic [31:0] i5,
  input logic [31:0] i4,
  input logic [31:0] i3,
  input logic [31:0] i2,
  input logic [31:0] i1,
  input logic [31:0] i0,
  input logic [31:0] z
);
  // RTL has no reset; pure combinational mux; default case drives zero; i31 is never selected.

  // When s==00001, z equals i0.
  check_sel_00001_to_i0: assert property (@(posedge clk) (s == 5'b00001) |-> (z == i0));

  // When s==00010, z equals i1.
  check_sel_00010_to_i1: assert property (@(posedge clk) (s == 5'b00010) |-> (z == i1));

  // When s==00011, z equals i2.
  check_sel_00011_to_i2: assert property (@(posedge clk) (s == 5'b00011) |-> (z == i2));

  // When s==00100, z equals i3.
  check_sel_00100_to_i3: assert property (@(posedge clk) (s == 5'b00100) |-> (z == i3));

  // When s==00101, z equals i4.
  check_sel_00101_to_i4: assert property (@(posedge clk) (s == 5'b00101) |-> (z == i4));

  // When s==00110, z equals i5.
  check_sel_00110_to_i5: assert property (@(posedge clk) (s == 5'b00110) |-> (z == i5));

  // When s==00111, z equals i6.
  check_sel_00111_to_i6: assert property (@(posedge clk) (s == 5'b00111) |-> (z == i6));

  // When s==01000, z equals i7.
  check_sel_01000_to_i7: assert property (@(posedge clk) (s == 5'b01000) |-> (z == i7));

  // When s==01001, z equals i8.
  check_sel_01001_to_i8: assert property (@(posedge clk) (s == 5'b01001) |-> (z == i8));

  // When s==01010, z equals i9.
  check_sel_01010_to_i9: assert property (@(posedge clk) (s == 5'b01010) |-> (z == i9));

  // When s==01011, z equals i10.
  check_sel_01011_to_i10: assert property (@(posedge clk) (s == 5'b01011) |-> (z == i10));

  // When s==01100, z equals i11.
  check_sel_01100_to_i11: assert property (@(posedge clk) (s == 5'b01100) |-> (z == i11));

  // When s==01101, z equals i12.
  check_sel_01101_to_i12: assert property (@(posedge clk) (s == 5'b01101) |-> (z == i12));

  // When s==01110, z equals i13.
  check_sel_01110_to_i13: assert property (@(posedge clk) (s == 5'b01110) |-> (z == i13));

  // When s==01111, z equals i14.
  check_sel_01111_to_i14: assert property (@(posedge clk) (s == 5'b01111) |-> (z == i14));

  // When s==10000, z equals i15.
  check_sel_10000_to_i15: assert property (@(posedge clk) (s == 5'b10000) |-> (z == i15));

  // When s==10001, z equals i16.
  check_sel_10001_to_i16: assert property (@(posedge clk) (s == 5'b10001) |-> (z == i16));

  // When s==10010, z equals i17.
  check_sel_10010_to_i17: assert property (@(posedge clk) (s == 5'b10010) |-> (z == i17));

  // When s==10011, z equals i18.
  check_sel_10011_to_i18: assert property (@(posedge clk) (s == 5'b10011) |-> (z == i18));

  // When s==10100, z equals i19.
  check_sel_10100_to_i19: assert property (@(posedge clk) (s == 5'b10100) |-> (z == i19));

  // When s==10101, z equals i20.
  check_sel_10101_to_i20: assert property (@(posedge clk) (s == 5'b10101) |-> (z == i20));

  // When s==10110, z equals i21.
  check_sel_10110_to_i21: assert property (@(posedge clk) (s == 5'b10110) |-> (z == i21));

  // When s==10111, z equals i22.
  check_sel_10111_to_i22: assert property (@(posedge clk) (s == 5'b10111) |-> (z == i22));

  // When s==11000, z equals i23.
  check_sel_11000_to_i23: assert property (@(posedge clk) (s == 5'b11000) |-> (z == i23));

  // When s==11001, z equals i24.
  check_sel_11001_to_i24: assert property (@(posedge clk) (s == 5'b11001) |-> (z == i24));

  // When s==11010, z equals i25.
  check_sel_11010_to_i25: assert property (@(posedge clk) (s == 5'b11010) |-> (z == i25));

  // When s==11011, z equals i26.
  check_sel_11011_to_i26: assert property (@(posedge clk) (s == 5'b11011) |-> (z == i26));

  // When s==11100, z equals i27.
  check_sel_11100_to_i27: assert property (@(posedge clk) (s == 5'b11100) |-> (z == i27));

  // When s==11101, z equals i28.
  check_sel_11101_to_i28: assert property (@(posedge clk) (s == 5'b11101) |-> (z == i28));

  // When s==11110, z equals i29.
  check_sel_11110_to_i29: assert property (@(posedge clk) (s == 5'b11110) |-> (z == i29));

  // When s==11111, z equals i30.
  check_sel_11111_to_i30: assert property (@(posedge clk) (s == 5'b11111) |-> (z == i30));

  // When s==00000 (default case), z is zero.
  check_sel_00000_to_zero: assert property (@(posedge clk) (s == 5'b00000) |-> (z == 32'h0000_0000));

endmodule