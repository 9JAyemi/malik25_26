module mag_comp #(
    parameter n = 8
)(
  input [n-1:0] A,
  input [n-1:0] B,
  output A_greater_than_B,
  output A_equal_to_B,
  output A_less_than_B
);


  reg [n-1:0] A_xor_B;
  reg [n-1:0] A_and_B;
  reg [n-1:0] A_greater_than_B_bits;
  reg [n-1:0] A_equal_to_B_bits;
  reg [n-1:0] A_less_than_B_bits;

  always @* begin
    A_xor_B = A ^ B;
    A_and_B = A & B;
    A_greater_than_B_bits = A & A_xor_B;
    A_equal_to_B_bits = ~A_xor_B & A_and_B;
    A_less_than_B_bits = B & A_xor_B;
  end

  assign A_greater_than_B = |A_greater_than_B_bits;
  assign A_equal_to_B = |A_equal_to_B_bits;
  assign A_less_than_B = |A_less_than_B_bits;

endmodule