
module adder32(
  input [31:0] a,
  input [31:0] b,
  input cin,
  output [31:0] sum,
  output cout
);
  wire [15:0] a_low, b_low, sum_low;
  wire [15:0] a_high, b_high, sum_high;
  wire c1, c2;

  assign a_low = a[15:0];
  assign b_low = b[15:0];
  assign a_high = a[31:16];
  assign b_high = b[31:16];

  // Low 16-bit adder
  adder16 adder_low(
    .a(a_low),
    .b(b_low),
    .cin(cin),
    .sum(sum_low),
    .cout(c1)
  );

  // High 16-bit adder
  adder16 adder_high(
    .a(a_high),
    .b(b_high),
    .cin(c1),
    .sum(sum_high),
    .cout(c2)
  );

  // Final 32-bit sum
  assign sum = {sum_high, sum_low};
  assign cout = c2;
endmodule
module adder16(
  input [15:0] a,
  input [15:0] b,
  input cin,
  output [15:0] sum,
  output cout
);
  wire [15:0] sum_temp;

  assign {cout, sum_temp} = a + b + cin;
  assign sum = sum_temp;
endmodule
module top_module(
  input [31:0] a,
  input [31:0] b,
  output [31:0] sum
);
  wire cin;
  wire cout;

  // Carry select adder
  adder32 adder(
    .a(a),
    .b(b),
    .cin(cin),
    .sum(sum),
    .cout(cout)
  );

  assign cin = 1'b0;
endmodule