


module MUXn_2_1(mux_in0, mux_in1, mux_sel, mux_out);

  parameter MuxLen = 63;

  output [MuxLen:0] mux_out;
  input [MuxLen:0] mux_in0;
  input [MuxLen:0] mux_in1;
  input mux_sel;

  reg [MuxLen:0] mux_out;

  always @(mux_in0 or mux_in1 or mux_sel)
  begin
    if (mux_sel == 1'b1)
      mux_out = mux_in1;
    else
      mux_out = mux_in0;
  end

endmodule 
module MUXn_4_1(mux_in0, mux_in1, mux_in2, mux_in3, mux_sel, mux_out);

  parameter MuxLen = 63;

  output [MuxLen:0] mux_out;
  input [MuxLen:0] mux_in0;
  input [MuxLen:0] mux_in1;
  input [MuxLen:0] mux_in2;
  input [MuxLen:0] mux_in3;
  input [1:0] mux_sel;

  wire [MuxLen:0] mux_tmp0;
  wire [MuxLen:0] mux_tmp1;

  MUXn_2_1 #(MuxLen) mux0(mux_in0, mux_in1, mux_sel[0], mux_tmp0);
  MUXn_2_1 #(MuxLen) mux1(mux_in2, mux_in3, mux_sel[0], mux_tmp1);
  MUXn_2_1 #(MuxLen) msel(mux_tmp0, mux_tmp1, mux_sel[1], mux_out);

  endmodule 
module MUXn_8_1(mux_in0, mux_in1, mux_in2, mux_in3, mux_in4, mux_in5, mux_in6, mux_in7, mux_sel, mux_out);

  parameter MuxLen = 63;

  output [MuxLen:0] mux_out;
  input [MuxLen:0] mux_in0;
  input [MuxLen:0] mux_in1;
  input [MuxLen:0] mux_in2;
  input [MuxLen:0] mux_in3;
  input [MuxLen:0] mux_in4;
  input [MuxLen:0] mux_in5;
  input [MuxLen:0] mux_in6;
  input [MuxLen:0] mux_in7;
  input [2:0] mux_sel;

  wire [MuxLen:0] mux_tmp0;
  wire [MuxLen:0] mux_tmp1;

  MUXn_4_1 #(MuxLen) mux0(mux_in0, mux_in1, mux_in2, mux_in3, mux_sel[1:0], mux_tmp0);
  MUXn_4_1 #(MuxLen) mux1(mux_in4, mux_in5, mux_in6, mux_in7, mux_sel[1:0], mux_tmp1);
  MUXn_2_1 #(MuxLen) msel(mux_tmp0, mux_tmp1, mux_sel[2], mux_out);

  endmodule 