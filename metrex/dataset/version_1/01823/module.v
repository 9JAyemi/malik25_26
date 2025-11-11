
module priority_encoder (
  input [3:0] in,
  output [1:0] out
);

  assign out = in[3] ? 2'b11 :
               in[2] ? 2'b10 :
               in[1] ? 2'b01 :
                            2'b00;

endmodule
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
module binary_multiplier (
  input [3:0] a,
  input [3:0] b,
  output [7:0] product
);

  wire [1:0] a_high, b_high;
  wire [3:0] a_shifted, b_shifted;
  wire [7:0] p0, p1, p2, p3;

  priority_encoder pe_a(.in(a), .out(a_high));
  priority_encoder pe_b(.in(b), .out(b_high));

  assign a_shifted = {b_high == 2'b00 ? 2'b00 : a[1:0], 2'b00};
  assign b_shifted = {a_high == 2'b00 ? 2'b00 : b[1:0], 2'b00};

  full_adder fa0(.a(a_shifted[0]), .b(b_shifted[0]), .cin(1'b0), .sum(p0[0]), .cout(p0[1]));
  full_adder fa1(.a(a_shifted[1]), .b(b_shifted[0]), .cin(p0[1]), .sum(p1[0]), .cout(p1[1]));
  full_adder fa2(.a(a_shifted[2]), .b(b_shifted[0]), .cin(p1[1]), .sum(p2[0]), .cout(p2[1]));
  full_adder fa3(.a(a_shifted[3]), .b(b_shifted[0]), .cin(p2[1]), .sum(p3[0]), .cout(p3[1]));

  assign product = {p3[1], p3[0], p2[0], p1[0], p0[0], 3'b000};

endmodule