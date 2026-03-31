module adder4 (
  input [3:0] a,
  input [3:0] b,
  input cin,
  output [3:0] sum,
  output cout
);

  wire [3:0] temp_sum;
  wire c1, c2, c3;

  // First stage of addition
  full_adder fa1(.a(a[0]), .b(b[0]), .cin(cin), .sum(temp_sum[0]), .cout(c1));

  // Second stage of addition
  full_adder fa2(.a(a[1]), .b(b[1]), .cin(c1), .sum(temp_sum[1]), .cout(c2));

  // Third stage of addition
  full_adder fa3(.a(a[2]), .b(b[2]), .cin(c2), .sum(temp_sum[2]), .cout(c3));

  // Fourth stage of addition
  full_adder fa4(.a(a[3]), .b(b[3]), .cin(c3), .sum(temp_sum[3]), .cout(cout));

  assign sum = temp_sum;

endmodule

module full_adder (
  input a,
  input b,
  input cin,
  output sum,
  output cout
);

  assign sum = a ^ b ^ cin;
  assign cout = (a & b) | (cin & a) | (cin & b);

endmodule