
module VoltageLevelShifter #(
  parameter n = 4, // number of input signals 
  parameter m = 2 // number of output signal
) (
  input [n-1:0] in,
  output [m-1:0] out
);


parameter V1 = 3.3; // input voltage level
parameter V2 = 5; // output voltage level

// calculate R1 based on input parameters
parameter R2 = 1000; // choose a value for R2
parameter R1 = (V2 - V1) / (V1 / R2);

// fixed implementation to avoid division
assign out = (in * R2) >> 10; // equivalent to out = (in * R2) / (R1 + R2)

endmodule