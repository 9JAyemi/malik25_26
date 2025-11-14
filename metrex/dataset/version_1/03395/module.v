
module adder_8bit(
  input [7:0] A,
  input [7:0] B,
  output [7:0] sum
);

  wire [7:0] temp_sum;
  wire carry_in = 1'b0;
  wire carry_out;

  assign temp_sum[0] = A[0] ^ B[0];
  assign carry_out = A[0] & B[0];

  genvar i;
  for (i = 1; i < 8; i = i + 1) begin : adder_loop
    assign temp_sum[i] = A[i] ^ B[i] ^ carry_in;
    assign carry_in = (A[i] & B[i]) | (A[i] & carry_out) | (B[i] & carry_out);
  end

  assign sum = temp_sum;

endmodule