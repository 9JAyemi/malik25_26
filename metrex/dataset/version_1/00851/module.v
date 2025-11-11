module barrel_shifter (
  input [7:0] in,
  input [1:0] shift_dir,
  input [2:0] shift_amt,
  output reg [7:0] out
);

parameter n = 8; // number of input and output signals
parameter s = 8; // maximum shift amount (power of 2)

reg [7:0] shifted_in;

always @(*) begin
  if (shift_dir == 0) // shift right
    shifted_in = {s{in[7]}}; // fill with MSB
  else // shift left
    shifted_in = {in, {s{1'b0}}}; // fill with 0s
  if (shift_amt > s) // shift amount too large
    out = {8{1'b0}}; // set output to 0
  else if (shift_amt == 0) // no shift
    out = in;
  else if (shift_dir == 0) // shift right
    out = shifted_in >> shift_amt;
  else // shift left
    out = shifted_in << shift_amt;
end

endmodule