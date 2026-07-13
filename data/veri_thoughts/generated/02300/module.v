
module MUXn_4_1(
  input [MuxLen:0] mux_in0,
  input [MuxLen:0] mux_in1,
  input [MuxLen:0] mux_in2,
  input [MuxLen:0] mux_in3,
  input [1:0] mux_sel,
  output [MuxLen:0] mux_out
);

  parameter MuxLen = 63;

  wire [MuxLen:0] mux_tmp0;
  wire [MuxLen:0] mux_tmp1;

  MUX2x1 #(MuxLen) mux0(mux_in0, mux_in1, mux_sel[0], mux_tmp0);
  MUX2x1 #(MuxLen) mux1(mux_in2, mux_in3, mux_sel[0], mux_tmp1);
  MUX2x1 #(MuxLen) msel(mux_tmp0, mux_tmp1, mux_sel[1], mux_out);

endmodule
module MUX2x1 #(
  parameter MuxLen = 0
)(
  input [MuxLen:0] in0,
  input [MuxLen:0] in1,
  input sel,
  output [MuxLen:0] out
);
  assign out = sel ? in1 : in0;
endmodule