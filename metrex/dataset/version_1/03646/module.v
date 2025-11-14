module div_module(
  input clk,
  input reset,
  input [7:0] in1,
  input [7:0] in2,
  output [15:0] out,
  output [7:0] remainder
);

  reg [15:0] quotient_reg;
  reg [7:0] remainder_reg;
  reg [7:0] in2_reg;
  reg [7:0] count_reg;
  wire [7:0] in1_reg;

  assign in1_reg = (count_reg == 0) ? in1 : quotient_reg[7:0];
  assign out = quotient_reg;
  assign remainder = remainder_reg;

  always @(posedge clk) begin
    if (reset) begin
      quotient_reg <= 16'd0;
      remainder_reg <= 8'd0;
      in2_reg <= 8'd0;
      count_reg <= 8'd0;
    end else begin
      if (count_reg == 0) begin
        in2_reg <= in2;
        quotient_reg[15:8] <= in1;
        quotient_reg[7:0] <= 8'd0;
        remainder_reg <= 8'd0;
      end else begin
        {quotient_reg[15:1], quotient_reg[0]} <= {quotient_reg[14:0], in1_reg[7]};
        remainder_reg <= {remainder_reg[6:0], in1_reg[7]} - in2_reg;
      end
      count_reg <= count_reg + 1;
    end
  end

endmodule