module RoundSaturation #(
  parameter integer IB = 4, // Number of integer bits
  parameter integer FB = 8 // Number of fractional bits
)(
  input signed [IB + FB - 1:0] in,
  output signed [IB + FB - 1:0] out
);


wire signed [IB + FB - 1:0] in_val;
wire signed [IB + FB - 1:0] round_val;
wire signed [IB + FB - 1:0] max_val;
wire signed [IB + FB - 1:0] min_val;

assign in_val = in * (2 ** FB); // Shift input to left by fb bits to convert to integer

assign round_val = (in_val >= 0) ? ((in_val + (2 ** (FB - 1))) >> FB) : ((in_val - (2 ** (FB - 1))) >> FB); // Round up/down based on fractional part

assign max_val = (2 ** (IB + FB - 1)) - 1; // Calculate maximum representable value
assign min_val = -(2 ** (IB + FB - 1)); // Calculate minimum representable value

assign out = (round_val > max_val) ? max_val : ((round_val < min_val) ? min_val : round_val); // Saturation: Output rounded value or max/min if out of range

endmodule
