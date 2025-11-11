module full_adder (
  output sum,
  output carry_out,
  input a,
  input b,
  input carry_in
);

  assign {carry_out, sum} = a + b + carry_in;

endmodule

module ripple_adder(
  output [3:0] sum,
  output cout,
  input [3:0] a,
  input [3:0] b,
  input cin
);

  wire [3:0] carry;
  full_adder fa0(sum[0], carry[0], a[0], b[0], cin);
  full_adder fa1(sum[1], carry[1], a[1], b[1], carry[0]);
  full_adder fa2(sum[2], carry[2], a[2], b[2], carry[1]);
  full_adder fa3(sum[3], cout, a[3], b[3], carry[2]);

endmodule