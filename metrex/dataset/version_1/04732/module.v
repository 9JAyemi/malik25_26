module top_module(
  input wire [15:0] in,
  input wire [1:0] en1,
  input wire en2,
  output wire [7:0] out_hi,
  output wire [7:0] out_lo
);

  wire [3:0] dec1_out;
  wire [15:0] dec2_out;
  wire [7:0] comp_hi;
  wire [7:0] comp_lo;

  decoder1 dec1(.in(en1), .enable(en2), .out(dec1_out));
  decoder2 dec2(.in(dec1_out), .enable(en2), .out(dec2_out));

  assign comp_hi = ~in[15:8];
  assign comp_lo = ~in[7:0];

  assign out_hi = en1 ? dec2_out[15:8] : 8'b0;
  assign out_lo = en1 ? comp_lo : comp_hi;

endmodule

module decoder1 (
  input [1:0] in,
  input enable,
  output [3:0] out
);
  assign out = enable ? {~in[1], ~in[0], in[1], in[0]} : 4'b0;
endmodule

module decoder2 (
  input [3:0] in,
  input enable,
  output [15:0] out
);
  assign out = enable ? {~in[3], ~in[2], ~in[1], ~in[0], in[3], in[2], in[1], in[0], ~in[3], ~in[2], ~in[1], in[0], in[3], in[2], in[1], ~in[0]} : 16'b0;
endmodule