module adder_4bit (
  input [3:0] a,
  input [3:0] b,
  input cin,
  output [3:0] sum,
  output cout
);

wire [3:0] c;
assign c[0] = cin;

full_adder fa0(a[0],b[0],c[0],sum[0],c[1]);
full_adder fa1(a[1],b[1],c[1],sum[1],c[2]);
full_adder fa2(a[2],b[2],c[2],sum[2],c[3]);
full_adder fa3(a[3],b[3],c[3],sum[3],cout);

endmodule
module full_adder (
  input a,
  input b,
  input cin,
  output sum,
  output cout
);

wire s1, s2;
assign s1 = a ^ b;
assign s2 = s1 ^ cin;
assign sum = s2;
assign cout = (a & b) | (s1 & cin);

endmodule
