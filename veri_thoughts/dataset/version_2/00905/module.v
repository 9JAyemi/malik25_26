module adder_4bit_carry (
  input [3:0] a,
  input [3:0] b,
  input cin,
  output [3:0] sum,
  output cout
);

  wire [3:0] s; // intermediate sum
  wire c1, c2, c3; // intermediate carry signals

  // generate the intermediate sum and carry signals
  full_adder fa0(a[0], b[0], cin, s[0], c1);
  full_adder fa1(a[1], b[1], c1, s[1], c2);
  full_adder fa2(a[2], b[2], c2, s[2], c3);
  full_adder fa3(a[3], b[3], c3, s[3], cout);

  // assign the outputs
  assign sum = s;

endmodule

// full adder module
module full_adder (
  input a,
  input b,
  input cin,
  output sum,
  output cout
);

  assign sum = a ^ b ^ cin;
  assign cout = (a & b) | (a & cin) | (b & cin);

endmodule