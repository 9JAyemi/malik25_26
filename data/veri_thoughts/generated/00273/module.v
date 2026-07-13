module eight_bit_adder (
  input [7:0] a,
  input [7:0] b,
  input carry_in,
  output [7:0] sum,
  output carry_out
);

  assign {carry_out, sum} = a + b + carry_in;

endmodule

module sixteen_bit_adder (
  input clk,
  input reset, // Synchronous active-high reset
  input [15:0] a,
  input [15:0] b,
  input carry_in,
  output [15:0] sum,
  output carry_out
);

  wire [7:0] adder1_sum;
  wire adder1_carry_out;
  wire [7:0] adder2_sum;
  wire adder2_carry_out;

  eight_bit_adder adder1(.a(a[7:0]), .b(b[7:0]), .carry_in(carry_in), .sum(adder1_sum), .carry_out(adder1_carry_out));
  eight_bit_adder adder2(.a(a[15:8]), .b(b[15:8]), .carry_in(adder1_carry_out), .sum(adder2_sum), .carry_out(adder2_carry_out));

  assign carry_out = adder2_carry_out;
  assign sum = {adder2_sum, adder1_sum};

endmodule