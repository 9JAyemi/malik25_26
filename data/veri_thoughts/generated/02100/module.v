
module byte_reverser (
  input [31:0] in,
  output [31:0] out
);
  assign out = {in[7:0], in[15:8], in[23:16], in[31:24]};
endmodule
module full_adder (
  input a, b, cin,
  output reg sum, carry_out
);
  always @ (a, b, cin) begin
    sum = a ^ b ^ cin;
    carry_out = (a & b) | (a & cin) | (b & cin);
  end
endmodule
module functional_module (
  input [31:0] in1,
  input [2:0] in2,
  output [31:0] out
);
  assign out = in1 ^ {in2[2], in2[2], in2[1:0]};
endmodule
module control_logic (
  input select,
  input [31:0] in1,
  input a, b, cin,
  output reg [31:0] out
);
  wire [31:0] in2;
  assign in2 = select ? {a, b, cin} : in1;

  byte_reverser byte_reverser_inst (
    .in(in2),
    .out(out)
  );
endmodule
module top_module (
  input clk,
  input reset,
  input [31:0] in,
  input a, b, cin,
  input select,
  output [31:0] out
);
  wire [31:0] in1;
  control_logic control_logic_inst (
    .select(select),
    .in1(in),
    .a(a),
    .b(b),
    .cin(cin),
    .out(in1)
  );

  assign out = in1;
endmodule