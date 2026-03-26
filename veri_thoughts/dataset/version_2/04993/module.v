
module full_adder(a, b, c_in, s, c_out);
  input a, b, c_in;
  output s, c_out;

  assign s = a ^ b ^ c_in;
  assign c_out = (a & b) | (a & c_in) | (b & c_in);
endmodule
module four_bit_adder(a, b, c_in, s, c_out);
  input [3:0] a, b;
  input c_in;
  output [3:0] s;
  output c_out;

  wire c1, c2, c3;
  full_adder fa1(a[0], b[0], c_in, s[0], c1);
  full_adder fa2(a[1], b[1], c1, s[1], c2);
  full_adder fa3(a[2], b[2], c2, s[2], c3);
  full_adder fa4(a[3], b[3], c3, s[3], c_out);
endmodule