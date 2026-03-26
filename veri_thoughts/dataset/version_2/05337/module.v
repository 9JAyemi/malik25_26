module four_bit_adder (
  input [3:0] a,
  input [3:0] b,
  input cin,
  output [3:0] sum,
  output cout
);

wire [3:0] c;
full_adder fa0(a[0], b[0], cin, sum[0], c[0]);
full_adder fa1(a[1], b[1], c[0], sum[1], c[1]);
full_adder fa2(a[2], b[2], c[1], sum[2], c[2]);
full_adder fa3(a[3], b[3], c[2], sum[3], cout);

endmodule
module full_adder (
  input a,
  input b,
  input cin,
  output sum,
  output cout
);

wire s1, c1, c2;
assign s1 = a ^ b;
assign sum = s1 ^ cin;
assign c1 = a & b;
assign c2 = s1 & cin;
assign cout = c1 | c2;

endmodule
