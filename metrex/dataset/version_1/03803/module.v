
module fp_add (
  input [31:0] a,
  input [31:0] b,
  output [31:0] c
);

  wire [31:0] a_mantissa;
  wire [31:0] b_mantissa;
  wire [7:0] a_exponent;
  wire [7:0] b_exponent;
  wire a_sign;
  wire b_sign;
  wire c_sign;
  wire [7:0] c_exponent;
  wire [31:0] c_mantissa;
  wire carry;
  wire [31:0] temp;

  assign a_mantissa = {1'b1, a[22:0]};
  assign b_mantissa = {1'b1, b[22:0]};
  assign a_exponent = a[30:23];
  assign b_exponent = b[30:23];
  assign a_sign = a[31];
  assign b_sign = b[31];

  assign {c_sign, c_exponent, c_mantissa, carry} =
    a_sign == b_sign ?
    {a_sign, a_exponent, a_mantissa + b_mantissa, 1'b0} :
    {a_mantissa > b_mantissa ? a_sign : b_sign,
     a_exponent > b_exponent ? a_exponent : b_exponent,
     a_mantissa > b_mantissa ? a_mantissa - b_mantissa : b_mantissa - a_mantissa,
     a_mantissa > b_mantissa ? 1'b0 : 1'b1};

  assign c = {c_sign, c_exponent, c_mantissa[22:0]};

endmodule
module fp_sub (
  input [31:0] a,
  input [31:0] b,
  output [31:0] c
);

  wire [31:0] a_mantissa;
  wire [31:0] b_mantissa;
  wire [7:0] a_exponent;
  wire [7:0] b_exponent;
  wire a_sign;
  wire b_sign;
  wire c_sign;
  wire [7:0] c_exponent;
  wire [31:0] c_mantissa;
  wire borrow;
  wire [31:0] temp;

  assign a_mantissa = {1'b1, a[22:0]};
  assign b_mantissa = {1'b1, b[22:0]};
  assign a_exponent = a[30:23];
  assign b_exponent = b[30:23];
  assign a_sign = a[31];
  assign b_sign = b[31];

  assign {c_sign, c_exponent, c_mantissa, borrow} =
    a_sign == b_sign ?
    {a_sign, a_exponent, a_mantissa + b_mantissa, 1'b0} :
    {a_mantissa > b_mantissa ? a_sign : !b_sign,
     a_exponent > b_exponent ? a_exponent : b_exponent,
     a_mantissa > b_mantissa ? a_mantissa - b_mantissa : b_mantissa - a_mantissa,
     a_mantissa > b_mantissa ? 1'b0 : 1'b1};

  assign c = {c_sign, c_exponent, c_mantissa[22:0]};

endmodule
module fp_mul (
  input [31:0] a,
  input [31:0] b,
  output [31:0] c
);

  wire [31:0] a_mantissa;
  wire [31:0] b_mantissa;
  wire [7:0] a_exponent;
  wire [7:0] b_exponent;
  wire a_sign;
  wire b_sign;
  wire c_sign;
  wire [7:0] c_exponent;
  wire [63:0] temp;

  assign a_mantissa = {1'b1, a[22:0]};
  assign b_mantissa = {1'b1, b[22:0]};
  assign a_exponent = a[30:23];
  assign b_exponent = b[30:23];
  assign a_sign = a[31];
  assign b_sign = b[31];
  assign temp = a_mantissa * b_mantissa;

  assign c_sign = a_sign ^ b_sign;
  assign c_exponent = a_exponent + b_exponent - 127;
  assign c = {c_sign, c_exponent, temp[54:23]};

endmodule