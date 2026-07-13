module dual_edge_ff (
  input clk,
  input data,
  output reg Q,
  output reg Q_bar
);

reg Q_temp;

always @(posedge clk) begin
  Q_temp <= data;
end

always @(negedge clk) begin
  Q <= Q_temp;
  Q_bar <= ~Q_temp;
end

endmodule
