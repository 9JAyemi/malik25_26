module ring_counter #(
  parameter n = 4 // number of output signals
)(
  input clk,
  output [n-1:0] out
);

reg [n-1:0] counter;

always @(posedge clk) begin
  counter <= {counter[n-2:0], counter[n-1]};
end

assign out = counter;

endmodule