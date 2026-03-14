
module adder4bit(
  input [3:0] a,
  input [3:0] b,
  input cin,
  output [3:0] sum,
  output cout
);

  wire [3:0] temp_sum;
  wire [3:0] temp_carry;

  // Full adder for the least significant bit
  full_adder fa0(
    .a(a[0]),
    .b(b[0]),
    .cin(cin),
    .sum(temp_sum[0]),
    .cout(temp_carry[0])
  );

  // Full adder for the second least significant bit
  full_adder fa1(
    .a(a[1]),
    .b(b[1]),
    .cin(temp_carry[0]),
    .sum(temp_sum[1]),
    .cout(temp_carry[1])
  );

  // Full adder for the third least significant bit
  full_adder fa2(
    .a(a[2]),
    .b(b[2]),
    .cin(temp_carry[1]),
    .sum(temp_sum[2]),
    .cout(temp_carry[2])
  );

  // Full adder for the most significant bit
  full_adder fa3(
    .a(a[3]),
    .b(b[3]),
    .cin(temp_carry[2]),
    .sum(temp_sum[3]),
    .cout(cout)
  );

  assign sum = temp_sum;

endmodule
module full_adder(
  input a,
  input b,
  input cin,
  output sum,
  output cout
);

  assign sum = a ^ b ^ cin;
  assign cout = (a & b) | (a & cin) | (b & cin);

endmodule