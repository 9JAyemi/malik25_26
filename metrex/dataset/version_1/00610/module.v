module accumulator #(
  parameter n = 4 // number of input signals
)(
  input [n-1:0] in,
  output reg [n:0] out
);

integer i;

always @(*) begin
  out = 0;
  for (i = 0; i < n; i = i + 1) begin
    out = out + in[i];
  end
end

endmodule