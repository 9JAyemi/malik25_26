module full_adder(
  input [15:0] in1,
  input [15:0] in2,
  input cin,
  output [15:0] out,
  output cout
);

  // Intermediate sum including carry-in
  wire [16:0] temp_out;

  // Perform the addition
  assign temp_out = {1'b0, in1} + {1'b0, in2} + cin;

  // Assign the lower 16 bits to the output
  assign out = temp_out[15:0];

  // The carry out is the 17th bit of the result
  assign cout = temp_out[16];

endmodule
