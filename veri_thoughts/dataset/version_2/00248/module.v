module four_bit_adder (
  input [3:0] a,
  input [3:0] b,
  input cin,
  output [3:0] sum,
  output cout
);

  wire [4:0] sum_temp;

  assign sum_temp = a + b + cin;

  assign sum = sum_temp[3:0];
  assign cout = sum_temp[4];

endmodule