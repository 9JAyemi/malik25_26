module floating_point_arithmetic (
  input [31:0] a,
  input [31:0] b,
  input [1:0] ctrl,
  output reg [31:0] result
);

parameter EXPONENT_WIDTH = 8;
parameter MANTISSA_WIDTH = 23;

// Define input and output formats as per IEEE 754 standard
wire [EXPONENT_WIDTH-1:0] a_exp, b_exp;
wire [MANTISSA_WIDTH-1:0] a_mant, b_mant;
wire a_sign, b_sign;
assign a_sign = a[31];
assign a_exp = a[30:23];
assign a_mant = a[22:0];
assign b_sign = b[31];
assign b_exp = b[30:23];
assign b_mant = b[22:0];

// Implement addition, subtraction, multiplication, and division using Verilog code
wire [31:0] add_result, sub_result, mul_result, div_result;
adder add(.a(a), .b(b), .result(add_result));
subtractor sub(.a(a), .b(b), .result(sub_result));
multiplier mul(.a(a), .b(b), .result(mul_result));
divider div(.a(a), .b(b), .result(div_result));

// Select the operation based on the control signal
always @(*) begin
  case (ctrl)
    2'b00: result <= add_result;
    2'b01: result <= sub_result;
    2'b10: result <= mul_result;
    2'b11: result <= div_result;
    default: result <= 32'b0;
  endcase
end

endmodule

module adder (
  input [31:0] a,
  input [31:0] b,
  output reg [31:0] result
);
always @* begin
  result = a + b;
end
endmodule

module subtractor (
  input [31:0] a,
  input [31:0] b,
  output reg [31:0] result
);
always @* begin
  result = a - b;
end
endmodule

module multiplier (
  input [31:0] a,
  input [31:0] b,
  output reg [31:0] result
);
always @* begin
  result = a * b;
end
endmodule

module divider (
  input [31:0] a,
  input [31:0] b,
  output reg [31:0] result
);
always @* begin
  result = a / b;
end
endmodule