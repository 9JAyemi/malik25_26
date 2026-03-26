module EchoCancellation #(
  parameter n = 16
) (
  input signed [n-1:0] s,
  input signed [n-1:0] e,
  output signed [n-1:0] f
);

assign f = s - e;

endmodule