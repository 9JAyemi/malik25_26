module modulo_operator (
  input [31:0] dividend,
  input [31:0] divisor,
  output reg [31:0] remainder
);

  // Calculate the quotient
  reg [31:0] quotient;
  always @* begin
    quotient = dividend / divisor;
  end

  // Calculate the product of the quotient and the divisor
  reg [31:0] product;
  always @* begin
    product = quotient * divisor;
  end

  // Subtract the product from the dividend to get the remainder
  always @* begin
    remainder = dividend - product;
  end

endmodule