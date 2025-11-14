module divider #(
  parameter n = 8 // number of bits in dividend and divisor
) (
  input signed [n-1:0] dividend,
  input signed [n-1:0] divisor,
  output signed [n-1:0] quotient,
  output signed [n-1:0] remainder
);

parameter signed_div = 1; // 1 for signed division, 0 for unsigned division

reg signed [n-1:0] dividend_reg;
reg signed [n-1:0] divisor_reg;
reg signed [n-1:0] quotient_reg;
reg signed [n-1:0] remainder_reg;
reg signed [n-1:0] dividend_abs;
reg signed [n-1:0] divisor_abs;
reg signed [n-1:0] quotient_abs;
reg signed [n-1:0] remainder_abs;
reg signed [n-1:0] dividend_sign;
reg signed [n-1:0] divisor_sign;
reg signed [n-1:0] quotient_sign;

always @(*) begin
  // Absolute value of dividend and divisor
  if (dividend < 0) begin
    dividend_abs = -dividend;
    dividend_sign = -1;
  end else begin
    dividend_abs = dividend;
    dividend_sign = 1;
  end
  
  if (divisor < 0) begin
    divisor_abs = -divisor;
    divisor_sign = -1;
  end else begin
    divisor_abs = divisor;
    divisor_sign = 1;
  end
  
  // Perform division
  if (divisor == 0) begin
    quotient_reg = 'bx;
    remainder_reg = 'bx;
  end else if (signed_div) begin
    // Signed division
    if (dividend_sign == divisor_sign) begin
      quotient_abs = dividend_abs / divisor_abs;
      remainder_abs = dividend_abs % divisor_abs;
      quotient_sign = dividend_sign;
    end else begin
      quotient_abs = (dividend_abs + divisor_abs - 1) / divisor_abs;
      remainder_abs = dividend_abs - quotient_abs * divisor_abs;
      quotient_sign = -dividend_sign;
    end
  end else begin
    // Unsigned division
    quotient_abs = dividend_abs / divisor_abs;
    remainder_abs = dividend_abs % divisor_abs;
    quotient_sign = 1;
  end
  
  // Apply sign to quotient and remainder
  quotient_reg = quotient_abs * quotient_sign;
  remainder_reg = remainder_abs * dividend_sign;
end

assign quotient = quotient_reg;
assign remainder = remainder_reg;

endmodule