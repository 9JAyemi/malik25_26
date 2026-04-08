
module mux_2to1(
  input [7:0] data0,
  input [7:0] data1,
  input sel,
  output [7:0] out
);

  assign out = sel ? data1 : data0;

endmodule

module mux_4to1_using_2to1 (
  input [7:0] data0,
  input [7:0] data1,
  input [7:0] data2,
  input [7:0] data3,
  input [1:0] sel,
  output [7:0] out
);

  wire [7:0] mux0_out;
  wire [7:0] mux1_out;

  mux_2to1 mux0(.data0(data0), .data1(data1), .sel(sel[0]), .out(mux0_out));
  mux_2to1 mux1(.data0(data2), .data1(data3), .sel(sel[0]), .out(mux1_out));

  assign out = sel[1] ? mux1_out : mux0_out;

endmodule
