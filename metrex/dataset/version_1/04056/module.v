
module adder_4bit(a, b, cin, sum, cout);
  input [3:0] a, b;
  input cin;
  output [3:0] sum;
  output cout;

  wire [2:0] c;  // Carry signals

  assign c[0] = cin;

  assign sum[0] = a[0] ^ b[0] ^ c[0];
  assign c[1] = (a[0] & b[0]) | (a[0] & c[0]) | (b[0] & c[0]);

  assign sum[1] = a[1] ^ b[1] ^ c[1];
  assign c[2] = (a[1] & b[1]) | (a[1] & c[1]) | (b[1] & c[1]);

  assign sum[2] = a[2] ^ b[2] ^ c[2];
  assign cout = (a[2] & b[2]) | (a[2] & c[2]) | (b[2] & c[2]);

  assign sum[3] = a[3] ^ b[3] ^ cout;
endmodule