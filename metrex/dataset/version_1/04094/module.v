
module mux4to1_decoder(
  input [3:0] sel,
  input [15:0] in,
  output reg [15:0] out
);

always @(*)
  case(sel)
    4'b0000: out = in[15:0];
    4'b0001: out = in[14:0];
    4'b0010: out = in[13:0];
    4'b0011: out = in[12:0];
    4'b0100: out = in[11:0];
    4'b0101: out = in[10:0];
    4'b0110: out = in[9:0];
    4'b0111: out = in[8:0];
    4'b1000: out = in[7:0];
    4'b1001: out = in[6:0];
    4'b1010: out = in[5:0];
    4'b1011: out = in[4:0];
    4'b1100: out = in[3:0];
    4'b1101: out = in[2:0];
    4'b1110: out = in[1:0];
    4'b1111: out = in[0];
  endcase

endmodule
module count_zeros(
  input [255:0] in,
  output reg out
);

integer i;
reg [7:0] count;

always @(*)
begin
  count = 0;
  for(i = 0; i < 256; i = i + 1)
  begin
    if(in[i] == 1'b0)
      count = count + 1;
  end
  if(count % 2 == 1)
    out = 1'b1;
  else
    out = 1'b0;
end

endmodule
module bitwise_or(
  input in1,
  input in2,
  output out
);

assign out = in1 | in2;

endmodule
module top_module(
  input [255:0] in,
  input [3:0] sel,
  output out
);

wire [15:0] mux_out;
wire count_out;

mux4to1_decoder mux(
   .sel(sel),
  .in({in[3:0], in[7:4], in[11:8], in[15:12]}),
  .out(mux_out)
);

count_zeros count(
  .in(in),
  .out(count_out)
);

bitwise_or or_gate(
  .in1(mux_out[0]),
  .in2(count_out),
  .out(out)
);

endmodule