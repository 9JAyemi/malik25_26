
module signed_non_restoring_divider (
  input signed [31:0] dividend,
  input signed [31:0] divisor,
  input clk,
  output reg signed [31:0] quotient
);

  reg signed [31:0] remainder;
  reg signed [31:0] dividend_reg;
  reg signed [31:0] divisor_reg;
  reg signed [31:0] quotient_reg;
  reg signed [31:0] adder_input;
  reg signed [31:0] adder_output;
  reg [4:0] count;
  reg sign;

  always @(*) begin
    dividend_reg = $signed({1'b0, {(dividend[31] ? 31'b1 : 31'b0)}, dividend[30:0]}); // Convert dividend to signed vector
    divisor_reg = $signed({1'b0, {(divisor[31] ? 31'b1 : 31'b0)}, divisor[30:0]});   // Convert divisor to signed vector
    sign = (dividend_reg < 0) ^ (divisor_reg < 0);
  end

  always @(posedge clk) begin
    if (count == 0) begin
      remainder = dividend_reg;
      quotient_reg = 0;
    end else begin
      if (remainder < 0) begin
        adder_input = divisor_reg - remainder;
        adder_output = remainder + adder_input;
        remainder = adder_output;
        quotient_reg[count-1] = 0;
      end else begin
        adder_input = remainder - divisor_reg;
        adder_output = remainder - adder_input;
        remainder = adder_output;
        quotient_reg[count-1] = 1;
      end
    end

    if (count == 16) begin
      quotient = $signed(quotient_reg);
    end

    count <= count + 1;
  end

endmodule
