
module udp_mux_4to1(
  output [3:0] out,
  input [3:0] in0, in1, in2, in3,
  input [1:0] sel
);

  wire mux_out0, mux_out1;

  mux_2to1 mux_2to10 (.out(mux_out0), .in0(in0[0]), .in1(in1[0]), .sel(sel[0]));
  mux_2to1 mux_2to11 (.out(mux_out1), .in0(in2[0]), .in1(in3[0]), .sel(sel[0]));

  mux_2to1 mux_2to12 (.out(out[0]), .in0(mux_out0), .in1(mux_out1), .sel(sel[1]));
  mux_2to1 mux_2to13 (.out(out[1]), .in0(in0[1]), .in1(in1[1]), .sel(sel[0]));
  mux_2to1 mux_2to14 (.out(out[2]), .in0(in2[2]), .in1(in3[2]), .sel(sel[0]));
  mux_2to1 mux_2to15 (.out(out[3]), .in0(in0[3]), .in1(in1[3]), .sel(sel[0]));

endmodule
module mux_2to1(
  output reg out,
  input in0, in1, sel
);

  always @(sel) begin
    case (sel)
      1'b0: out = in0;
      1'b1: out = in1;
    endcase
  end

endmodule